
#include "postgres.h"
#include "miscadmin.h"
#include "fmgr.h"
#include "pgstat.h"
#include <sys/time.h>
#include <time.h> 
#include <math.h>

#include "utils/elog.h"
#include "utils/geo_decls.h"
#include "utils/lsyscache.h"
#include "utils/relcache.h"
#include "utils/rel.h"
#include "utils/memutils.h"
#include "utils/builtins.h"
#include "utils/geo_decls.h"
#include "utils/datum.h"
#include "utils/index_selfuncs.h"


PG_FUNCTION_INFO_V1(myspgist_point_distance);
Datum  myspgist_point_distance(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(myspghandler);
extern Datum myspghandler(PG_FUNCTION_ARGS);