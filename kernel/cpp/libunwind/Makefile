#
# libunwind
#

# unwind
obj-y += unwind/Backtrace.o unwind/DeleteException.o
obj-y += unwind/FindEnclosingFunction.o unwind/ForcedUnwind.o unwind/GetBSP.o
obj-y += unwind/GetCFA.o unwind/GetDataRelBase.o unwind/GetGR.o unwind/GetIP.o
obj-y += unwind/GetIPInfo.o unwind/GetLanguageSpecificData.o
obj-y += unwind/GetRegionStart.o unwind/GetTextRelBase.o unwind/RaiseException.o
obj-y += unwind/Resume.o unwind/Resume_or_Rethrow.o unwind/SetGR.o
obj-y += unwind/SetIP.o

# dwarf
obj-y += dwarf/Gexpr.o dwarf/Gfde.o dwarf/Gfind_proc_info-lsb.o
obj-y += dwarf/Gfind_unwind_table.o dwarf/Gparser.o dwarf/Gpe.o dwarf/Gstep.o
obj-y += dwarf/global.o

# mi
obj-y += mi/Gdestroy_addr_space.o mi/Gdyn-extract.o mi/Gfind_dynamic_proc_info.o
obj-y += mi/Gget_accessors.o mi/Gget_fpreg.o mi/Gget_proc_info_by_ip.o
obj-y += mi/Gget_proc_name.o mi/Gget_reg.o mi/Gput_dynamic_unwind_info.o
obj-y += mi/Gset_caching_policy.o mi/Gset_fpreg.o mi/Gset_reg.o
obj-y += mi/dyn-info-list.o mi/flush_cache.o mi/init.o mi/mempool.o

# x86-64
obj-$(CONFIG_X86_64) += x86_64/Gcreate_addr_space.o x86_64/Gget_proc_info.o
obj-$(CONFIG_X86_64) += x86_64/Gget_save_loc.o x86_64/Gglobal.o x86_64/Ginit.o
obj-$(CONFIG_X86_64) += x86_64/Ginit_local.o x86_64/Ginit_remote.o
obj-$(CONFIG_X86_64) += x86_64/Gos-linux.o x86_64/Gregs.o x86_64/Gresume.o
obj-$(CONFIG_X86_64) += x86_64/Gstash_frame.o x86_64/Gstep.o x86_64/Gtrace.o
obj-$(CONFIG_X86_64) += x86_64/getcontext.o x86_64/is_fpreg.o x86_64/longjmp.o
obj-$(CONFIG_X86_64) += x86_64/regname.o x86_64/setcontext.o x86_64/siglongjmp.o

# ccflags
ccflags-y += -I$(src) -I$(src)/tdep -I$(src)/dwarf
ccflags-y += -DUNW_LOCAL_ONLY
ccflags-y += -DPACKAGE_STRING=\"libunwind-linux-kernel\"
ccflags-y += -DPACKAGE_BUGREPORT=\"vegard.nossum@oracle.com\"
ccflags-$(CONFIG_CPP_LIBUNWIND_DEBUG) += -DDEBUG
