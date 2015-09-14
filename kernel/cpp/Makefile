#
# C++ support (exceptions, RTTI, etc.)
#

# libcxxrt
obj-y += $(addprefix libcxxrt/src/,dynamic_cast.o exception.o guard.o stdexcept.o typeinfo.o memory.o auxhelper.o libelftc_dem_gnu3.o)

# libunwind
obj-y += $(patsubst $(src)/%.c,%.o,$(wildcard $(src)/libunwind/src/unwind/*.c))
obj-y += $(patsubst $(src)/%.c,%.o,$(wildcard $(src)/libunwind/src/dwarf/L*.c)) libunwind/src/dwarf/global.o
obj-y += $(patsubst $(src)/%.c,%.o,$(filter-out %/Ldyn-remote.c,$(wildcard $(src)/libunwind/src/mi/L*.c)))
obj-y += $(addprefix libunwind/src/mi/,init.o mempool.o flush_cache.o dyn-info-list.o)
obj-$(CONFIG_X86_64) += $(patsubst $(src)/%.c,%.o,$(filter-out %-freebsd.c,$(wildcard $(src)/libunwind/src/x86_64/L*.c)))
obj-$(CONFIG_X86_64) += $(patsubst $(src)/%.S,%.o,$(wildcard $(src)/libunwind/src/x86_64/*.S))
obj-$(CONFIG_X86_64) += $(addprefix libunwind/src/x86_64/,is_fpreg.o regname.o)

ccflags-y := -I$(src)/libunwind/include/ -I$(src)/libunwind/include/tdep/ -I$(src)/libunwind/src/
#ccflags-y += -DDEBUG
ccflags-y += -DUNW_LOCAL_ONLY
ccflags-y += -DPACKAGE_STRING=\"libunwind-linux-kernel\"
ccflags-y += -DPACKAGE_BUGREPORT=\"vegard.nossum@oracle.com\"
