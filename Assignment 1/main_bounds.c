#include "wrapped_fs.h"

int main() {
	init_fs();
	int c = nondet_int();
	int d1 = open_dir(c, "test");
	//assert(d1 < 0);
	return 0;
}
