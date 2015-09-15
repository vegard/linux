#include <linux/cpp/PROTECT.h>
#include <linux/init.h>
#include <linux/printk.h>
#include <linux/cpp/PROTECT.h>

#include <linux/cpp/spinlock.h>

struct error {
	int x;

	error(int x): x(x) {}
};

class KernelClass {
public:
	int value;
	Spinlock lock;

	KernelClass():
		value(100)
	{
	}

	void foo()
	{
		//throw error(123);
		throw 10;
	}
};

static int __init cpp_init()
{
	KernelClass kernel_class;

	{
		SpinlockIRQSaveLocker locker(kernel_class.lock);

		printk(KERN_ERR "cpp_init: %u, locked? %s\n",
			kernel_class.value,
			kernel_class.lock.is_locked() ? "yes" : "no");

		try {
			kernel_class.foo();
		} catch (const error &e) {
			printk(KERN_ERR "cpp_init(): caught error with value %d\n", e.x);
		} catch (const int x) {
			printk(KERN_ERR "cpp_init(): caught int with value %d\n", x);
		}
	}

	return 0;
}

late_initcall(cpp_init)
