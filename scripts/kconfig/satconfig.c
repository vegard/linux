#define _GNU_SOURCE
#include <assert.h>
#include <locale.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define LKC_DIRECT_LINK
#include "lkc.h"
#include "satconf.h"

int main(int argc, char *argv[])
{
	bool randomize = false;

	setlocale(LC_ALL, "");
	bindtextdomain(PACKAGE, LOCALEDIR);
	textdomain(PACKAGE);

	int optind = 1;
	if (!strcmp(argv[optind], "--random")) {
		randomize = true;
		++optind;
	}

	const char *Kconfig_file = "Kconfig";
	if (optind < argc)
		Kconfig_file = argv[optind++];

	const char *satconfig_file = ".satconfig";
	if (optind < argc)
		satconfig_file = argv[optind++];

	satconfig_init(Kconfig_file, randomize);

	/* We need to override the S_DEF_USER values from the default
	 * configuration with the corresponding values from .satconfig,
	 * because S_DEF_USER influences the operation of the main kconfig
	 * machinery. */
	conf_read_simple(satconfig_file, S_DEF_USER);
	conf_read_simple(satconfig_file, S_DEF_SAT);

	satconfig_update_all_symbols();

	satconfig_solve();

	if (conf_write(NULL)) {
		fprintf(stderr, "error: writing .config\n");
		exit(EXIT_FAILURE);
	}

#if 0 /* XXX: Let the build system take care of this. */
	if (conf_write_autoconf()) {
		fprintf(stderr, "error: writing autoconf.h\n");
		exit(EXIT_FAILURE);
	}

	{
		/* Check that none of the symbol values changed while writing
		 * out the configuration files. */
		unsigned int i;
		struct symbol *sym;
		for_all_symbols(i, sym) {
			if (!sym->name)
				continue;
			if (sym->type != S_BOOLEAN && sym->type != S_TRISTATE)
				continue;

			{
				int y = picosat_deref(sym_y(sym));
				assert(y != 0);

				if (y == 1) {
					if (sym->type == S_TRISTATE) {
						int m = picosat_deref(sym_m(sym));
						assert(m != 0);

						if (m == 1)
							check_sym_value(sym, mod);
						else if (m == -1)
							check_sym_value(sym, yes);
					} else {
						check_sym_value(sym, yes);
					}
				} else if (y == -1) {
					if (sym->type == S_TRISTATE) {
						int m = picosat_deref(sym_m(sym));
						assert(m == -1);
					}

					check_sym_value(sym, no);
				}
			}
		}

		if (nr_changed) {
			fprintf(stderr, "warning: %u symbols differ "
				"from their SAT assignments\n", nr_changed);
		}
	}
#endif

	return EXIT_SUCCESS;
}

