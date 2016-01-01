#ifndef SATCONF_H
#define SATCONF_H

struct symbol;

void satconfig_init(const char *Kconfig_file, bool randomize);
void satconfig_update_symbol(struct symbol *sym);
void satconfig_update_all_symbols(void);
void satconfig_solve(void);

#endif
