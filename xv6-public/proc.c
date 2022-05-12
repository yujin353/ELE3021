#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"

int num_lwp = 0;
int nextlwpid = 1;

struct st {
	int use;
};

struct {
	struct st st[NPROC*50];
} stable;

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

static struct proc *initproc;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Must be called with interrupts disabled
int
cpuid() {
  return mycpu()-cpus;
}

// Must be called with interrupts disabled to avoid the caller being
// rescheduled between reading lapicid and running through the loop.
struct cpu*
mycpu(void)
{
  int apicid, i;
  
  if(readeflags()&FL_IF)
    panic("mycpu called with interrupts enabled\n");
  
  apicid = lapicid();
  // APIC IDs are not guaranteed to be contiguous. Maybe we should have
  // a reverse map, or reserve a register to store &cpus[i].
  for (i = 0; i < ncpu; ++i) {
    if (cpus[i].apicid == apicid)
      return &cpus[i];
  }
  panic("unknown apicid\n");
}

// Disable interrupts so that we are not rescheduled
// while reading proc from the cpu structure
struct proc*
myproc(void) {
  struct cpu *c;
  struct proc *p;
  pushcli();
  c = mycpu();
  p = c->proc;
  popcli();
  return p;
}

//PAGEBREAK: 32
// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;

  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;

  p->level = 0;
  p->priority = 0;
  p->usedtick = 0;

  p->lwpid = 0;
  p->lwppid = 0;
  p->retval = 0;
  p->sbase = 0;
  p->snum = 0;
  p->forked = 0;

  release(&ptable.lock);

  // Allocate kernel stack.
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;

  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe*)sp;

  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint*)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context*)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;

  return p;
}

//PAGEBREAK: 32
// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];

  p = allocproc();
  
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  // this assignment to p->state lets other cores
  // run this process. the acquire forces the above
  // writes to be visible, and the lock is also needed
  // because the assignment might not be atomic.
  acquire(&ptable.lock);

  p->state = RUNNABLE;

  release(&ptable.lock);
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  struct proc *curproc = myproc();
  struct proc *p;

  acquire(&ptable.lock);

  sz = curproc->sz;
  if(n > 0){
    if((sz = allocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  curproc->sz = sz;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
	  if(p->lwppid == curproc->lwppid || p->pid == curproc->lwppid)
		  if(curproc->lwppid > 0)
			  p->sz = curproc->sz;
  release(&ptable.lock);

  switchuvm(curproc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *curproc = myproc();

  // Allocate process.
  if((np = allocproc()) == 0){
    return -1;
  }

  if(curproc->lwpid > 0) {
	  np->forked = 1;
	  np->lwpid = nextlwpid++;
  }

  // Copy process state from proc.
  if((np->pgdir = copyuvm(curproc->pgdir, curproc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }
  np->sz = curproc->sz;
  np->parent = curproc;
  *np->tf = *curproc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for(i = 0; i < NOFILE; i++)
    if(curproc->ofile[i])
      np->ofile[i] = filedup(curproc->ofile[i]);
  np->cwd = idup(curproc->cwd);

  safestrcpy(np->name, curproc->name, sizeof(curproc->name));

  pid = np->pid;

  acquire(&ptable.lock);

  np->state = RUNNABLE;

  release(&ptable.lock);

  return pid;
}

int
isLWP(struct proc *t)
{
	struct proc *p;
	struct proc *curproc = myproc();

	if (curproc->lwppid > 0)
		return 1;
	for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
	    if(p->lwppid == t->lwppid)
			return 1;
	return 0;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *curproc = myproc();
  struct proc *p;
  int fd;

  if(curproc == initproc)
    panic("init exiting");

  if(curproc->lwpid == 0){
	curproc->killed = 1;

	acquire(&ptable.lock);

	for(;;) {
	  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
		if(p->lwppid == curproc->pid) {
		  if(p->state == ZOMBIE) {
			kfree(p->kstack);
			p->kstack = 0;
			deallocuvm(p->pgdir, p->sbase+2*PGSIZE, p->sbase);
			p->pid = 0;
			p->parent = 0;
			p->name[0] = 0;
			p->killed = 0;
			p->state = UNUSED;

			p->lwpid = 0;
			p->lwppid = 0;
			p->sbase = 0;
			p->snum = 0;
			p->forked = 0;
			p->retval = 0;

			num_lwp--;
		  } else {
			p->killed = 1;
			wakeup1(p);
		  }
		}
	  }
	  if(num_lwp == 0) {
		  release(&ptable.lock);
		  break;
	  }
	  sleep(curproc, &ptable.lock);
	}
  } else if(curproc->forked != 1) {
	  curproc->parent->killed = 1;
  }

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd]){
      fileclose(curproc->ofile[fd]);
      curproc->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(curproc->cwd);
  end_op();
  curproc->cwd = 0;

  acquire(&ptable.lock);

  if(curproc->lwpid == 0) {
	wakeup1(curproc->parent);
  } else {
	  if(curproc->parent != 0)
		  wakeup1(curproc->parent);
  }

  // Parent might be sleeping in wait().
  wakeup1(curproc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == curproc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.
  curproc->state = ZOMBIE;
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;
  struct proc *curproc = myproc();
 
  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != curproc)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        p->state = UNUSED;
        release(&ptable.lock);
        return pid;
      }
    }
    // No point waiting if we don't have any children.

    if(!havekids || curproc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(curproc, &ptable.lock);  //DOC: wait-sleep
  }
}

//PAGEBREAK: 42
// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.


#ifdef ML_SCHED
void
scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();
  c->proc = 0;

  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
	int even = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->pid % 2 == 0 && p->state == RUNNABLE){
		  even = 1;
		  break;
	  }
	}
	for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
		if(p->state != RUNNABLE)
			continue;
		if(even == 0){
			if(p->pid % 2 == 0)
				continue;
		}
		else{
			if(p->pid % 2 == 1)
				continue;
		}
		c->proc = p;
		switchuvm(p);
		p->state = RUNNING;
		swtch(&(c->scheduler), p->context);
		switchkvm();
		c->proc = 0;
		if(even == 0)
			break;
	}
	release(&ptable.lock);
  }
}
#elif MLFQ_SCHED
void
scheduler(void)
{
  struct proc *p;
  struct proc *slct_p;
  struct cpu *c = mycpu();
  c->proc = 0;
  int priorityBoost = 0;

  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
	slct_p = 0;
	
	for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
         if(p->state != RUNNABLE || p->level == MLFQ_K)
             continue;
		 if(slct_p == 0)
		 	slct_p = p;
		 else{
			 if(slct_p->level > p->level){
				 slct_p = p;
			 }
			 else if(slct_p->level == p->level){
				 if(p->usedtick != 0){
					 slct_p = p;
				 }
				 else{
					if((slct_p->usedtick == 0) && (slct_p->priority < p->priority)){
                             slct_p = p;
                    }
				 }
			 }
		 }
	}
	p = slct_p;

	if(p != 0){
		c->proc = p;
	    switchuvm(p);
    	p->state = RUNNING;
	    swtch(&(c->scheduler), p->context);
	    switchkvm();
		
	    c->proc = 0;
		if(p->usedtick >= ((p->level)*4 + 2)){
			p->level++;
			p->usedtick = 0;
		}
	}
	priorityBoost++;
	if(priorityBoost >= 100){
		for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
            p->level = 0;
            p->usedtick = 0;
         }
		priorityBoost = 0;
	}
	release(&ptable.lock);

  }
}

#else
void
scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();
  c->proc = 0;
  
  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->state != RUNNABLE)
        continue;

      // Switch to chosen process.  It is the process's job
      // to release ptable.lock and then reacquire it
      // before jumping back to us.
      c->proc = p;
      switchuvm(p);
      p->state = RUNNING;

      swtch(&(c->scheduler), p->context);
      switchkvm();

      // Process is done running for now.
      // It should have changed its p->state before coming back.
      c->proc = 0;
    }
    release(&ptable.lock);

  }
}
#endif

uint
get_base(struct proc *p) {
	for(uint i = 0; i < NPROC*50; i++) {
		if(stable.st[i].use != 0)
			continue;

		stable.st[i].use = 1;
		p->snum = i;

		return i;
	}
	panic("get_base() panic");
}

int
thread_create(thread_t* thread, void* (*start_routine)(void*), void* arg){
	int i;
	struct proc *np;
	struct proc *curproc = myproc();

	if((np = allocproc()) == 0)
		return -1;

	num_lwp++;

	acquire(&ptable.lock);

	if(curproc->lwpid > 0) {
		np->lwppid = curproc->lwppid;
		np->parent = curproc->parent;
	} else if(curproc->lwpid == 0) {
		np->lwppid = curproc->pid;
		np->parent = curproc;
	} else {
		cprintf("curproc->lwpid < 0");
		return -1;
	}

	np->lwpid = nextlwpid++;
	*thread = np->lwpid;

	np->pgdir = curproc->pgdir;
	*np->tf = *curproc->tf;
	safestrcpy(np->name, curproc->name, sizeof(curproc->name));
	np->cwd = idup(curproc->cwd);

	np->sbase = curproc->sz + (uint)(2*PGSIZE*(get_base(np)+1));

	if((np->sz = allocuvm(np->pgdir, np->sbase, np->sbase + 2*PGSIZE)) == 0){
		np->state = UNUSED;
		return -1;
	}

	np->tf->esp = np->sz - 4;
	*((uint*)(np->tf->esp)) = (uint)arg;
	np->tf->esp = np->sz - 8;
	*((uint*)(np->tf->esp)) = 0xffffffff;

	np->tf->eip = (uint)start_routine;

	struct proc *p;

	for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
		if(p->parent->pid == np->parent->pid)
			p->sz = np->sz;

	for(i=0; i<NOFILE; i++)
		if(curproc->ofile[i])
			np->ofile[i] = filedup(curproc->ofile[i]);

	np->state = RUNNABLE;
	release(&ptable.lock);

	return 0;
}

void
thread_exit(void* retval) {
	struct proc *curproc = myproc();
	int fd;

	if(curproc == initproc)
		panic("init exiting\n");

	for(fd = 0; fd < NOFILE; fd++) {
		if(curproc->ofile[fd]) {
			fileclose(curproc->ofile[fd]);
			curproc->ofile[fd] = 0;
		}
	}

	begin_op();
	iput(curproc->cwd);
	end_op();
	curproc->cwd = 0;

	acquire(&ptable.lock);

	curproc->retval = retval;

	wakeup1(curproc->parent);

	curproc->state = ZOMBIE;
	num_lwp--;

	sched();

	cprintf("curproc->state: %d\n", curproc->state);
	cprintf("curproc->lwppid: %d\n", curproc->lwppid);
	cprintf("curproc->lwpid: %d\n", curproc->lwpid);
	cprintf("curproc->pid: %d\n", curproc->pid);
	cprintf("num_lwp: %d\n", num_lwp);

	panic("zombie exit\n");
}

int
thread_join(thread_t thread, void** retval) {
	struct proc *p;
	struct proc *curproc = myproc();

	if(curproc->lwpid != 0) {
		cprintf("curproc not a manager\n");
		return -1;
	}

	acquire(&ptable.lock);

	for(;;) {
		for(p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
			if(p->lwpid != thread)
				continue;
			if(p->lwppid != curproc->pid)
				continue;

			if(p->state == ZOMBIE) {
				*retval = p->retval;

				kfree(p->kstack);
				p->kstack = 0;
				deallocuvm(p->pgdir, p->sbase+2*PGSIZE, p->sbase);

				stable.st[p->snum].use = 0;

				p->pid = 0;
				p->parent = 0;
				p->name[0] = 0;
				p->killed = 0;
				p->state = UNUSED;

				p->lwpid = 0;
				p->lwppid = 0;
				p->sbase = 0;
				p->snum = 0;
				p->forked = 0;
				p->retval = 0;

				release(&ptable.lock);

				return 0;
			}
		}

		if(curproc->killed) {
			release(&ptable.lock);
			return -1;
		}
		sleep(curproc, &ptable.lock);
	}
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->ncli, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(mycpu()->ncli != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = mycpu()->intena;
  swtch(&p->context, mycpu()->scheduler);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  myproc()->state = RUNNABLE;
#ifdef MLFQ_SCHED
  myproc()->usedtick++;
#endif
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  if (first) {
    // Some initialization functions must be run in the context
    // of a regular process (e.g., they call sleep), and thus cannot
    // be run from main().
    first = 0;
    iinit(ROOTDEV);
    initlog(ROOTDEV);
  }

  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();
  
  if(p == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }
  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
	  if(p->pid == pid){
		  p->killed = 1;
		  // Wake process from sleep if necessary.
		  if(p->state == SLEEPING)
			  p->state = RUNNABLE;
		  release(&ptable.lock);
		  return 0;
	  }
  }

/*  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->lwppid == pid ) {
          p->killed = 1;
          if(p->state == SLEEPING) {
              p->state = RUNNABLE;
          }
      }
  }
*/
  release(&ptable.lock);
  return -1;
}

//PAGEBREAK: 36
// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}

int
getlev(void)
{
	return myproc()->level;
}

int
setpriority(int pid, int priority)
{
	struct proc *curproc = myproc();
	struct proc *p;

	if(priority < 0 || priority > 10)
		return -2;

	acquire(&ptable.lock);
	for(p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
		if(p->pid == pid){
			if(curproc->pid == p->parent->pid){
				p->priority = priority;
				release(&ptable.lock);
				return 0;
			}
		}
	}
	release(&ptable.lock);
	return -1;
}
