/* This file exists to protect C headers included in C++ source files.
 * The problem with C headers is that they use C++ keywords as identifiers,
 * so the trick we use to get around most of those issues is to temporarily
 * redefine them during preprocessing, and then restore (undefine) them
 * after all the headers have been included.
 *
 * Example usage:
 *
 * #include <linux/cpp/PROTECT.h>
 * #include <linux/bug.h>
 * #include <linux/kernel.h>
 * #include <linux/cpp/PROTECT.h>
 */

#ifndef LINUX_CPP_PROTECT_H
#define LINUX_CPP_PROTECT_H

#ifndef __cplusplus
#error This header can only be included in C++ sources
#endif

/* Header */
extern "C" {
#define and and_
#define class class_
#define namespace namespace_
#define new new_
#define private private_

/* Needed because it's too magic. */
#define PG_private PG_private_

#else
#undef LINUX_CPP_PROTECT_H

/* Footer */
#undef and
#undef class
#undef namespace
#undef new
#undef private

#undef PG_private
}

#endif
