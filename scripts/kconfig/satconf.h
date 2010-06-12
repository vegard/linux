#ifndef SATCONF_H
#define SATCONF_H

struct symbol;

extern unsigned int satconfig_core_size;
extern const char **satconfig_core;

void satconfig_init(const char *Kconfig_file, bool randomize);
void satconfig_update_symbol(struct symbol *sym);
void satconfig_update_all_symbols(void);
bool satconfig_solve(void);
void satconfig_check_config(void);

#endif
