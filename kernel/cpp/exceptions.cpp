extern "C" {
#include <linux/bug.h>
}

extern "C" void _Unwind_Resume(void)
{
	/* Not supported yet. */
	BUG();
}

