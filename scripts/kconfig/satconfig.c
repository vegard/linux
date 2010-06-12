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

	if (satconfig_solve()) {
		if (conf_write(NULL)) {
			fprintf(stderr, "error: writing .config\n");
			exit(EXIT_FAILURE);
		}

		if (conf_write_autoconf(0)) {
			fprintf(stderr, "error: writing autoconf.h\n");
			exit(EXIT_FAILURE);
		}

		satconfig_check_config();
	} else {
		fprintf(stderr, "error: no possible solutions\n");
		exit(EXIT_FAILURE);
	}

	return EXIT_SUCCESS;
}
