#include "types.h"
#include "stat.h"
#include "user.h"

int
main(int argc, char *argv[])
{
	int pid;
	pid = fork();

	for(;;) {
		if(pid < 0) {
			printf(1, "Fork Failed\n");
			exit();
		}
		else if(pid == 0) {
			printf(1, "child\n");
			yield();
		}
		else {
			printf(1, "parent\n");
			yield();
		}
	}
};
