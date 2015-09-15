#ifndef __LINUX_CPP_SPINLOCK_H
#define __LINUX_CPP_SPINLOCK_H

#include <linux/cpp/PROTECT.h>
#include <linux/spinlock.h>
#include <linux/cpp/PROTECT.h>

class Spinlock {
public:
	spinlock_t spinlock;

	Spinlock()
	{
		spin_lock_init(&spinlock);
	}

	~Spinlock()
	{
	}

	bool is_locked() const
	{
		return spin_is_locked(&spinlock);
	}

	void lock()
	{
		spin_lock(&spinlock);
	}

	void unlock()
	{
		spin_unlock(&spinlock);
	}

	void lock_irq()
	{
		spin_lock_irq(&spinlock);
	}

	void unlock_irq()
	{
		spin_unlock_irq(&spinlock);
	}

	void lock_irqsave(unsigned long &flags)
	{
		spin_lock_irqsave(&spinlock, flags);
	}

	void unlock_irqrestore(unsigned long &flags)
	{
		spin_unlock_irqrestore(&spinlock, flags);
	}
};

class SpinlockLocker {
public:
	Spinlock &spinlock;

	SpinlockLocker(Spinlock &spinlock):
		spinlock(spinlock)
	{
		spinlock.lock();
	}

	~SpinlockLocker()
	{
		spinlock.unlock();
	}
};

class SpinlockIRQLocker {
public:
	Spinlock &spinlock;

	SpinlockIRQLocker(Spinlock &spinlock):
		spinlock(spinlock)
	{
		spinlock.lock_irq();
	}

	~SpinlockIRQLocker()
	{
		spinlock.unlock_irq();
	}
};

class SpinlockIRQSaveLocker {
public:
	Spinlock &spinlock;
	unsigned long flags;

	SpinlockIRQSaveLocker(Spinlock &spinlock):
		spinlock(spinlock)
	{
		spinlock.lock_irqsave(flags);
	}

	~SpinlockIRQSaveLocker()
	{
		spinlock.unlock_irqrestore(flags);
	}
};

#endif
