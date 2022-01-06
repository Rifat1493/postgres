/*-------------------------------------------------------------------------
 *
 * geo_selfuncs.c
 *	  Selectivity routines registered in the operator catalog in the
 *	  "oprrest" and "oprjoin" attributes.
 *
 * Portions Copyright (c) 1996-2020, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/utils/adt/geo_selfuncs.c
 *
 *	XXX These are totally bogus.  Perhaps someone will make them do
 *	something reasonable, someday.
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "utils/builtins.h"
#include "utils/geo_decls.h"
#include "access/htup_details.h"
#include "catalog/pg_statistic.h"
#include "nodes/pg_list.h"
#include "optimizer/pathnode.h"
#include "optimizer/optimizer.h"
#include "utils/lsyscache.h"
#include "utils/typcache.h"
#include "utils/selfuncs.h"
#include "utils/rangetypes.h"

/*
 *	Selectivity functions for geometric operators.  These are bogus -- unless
 *	we know the actual key distribution in the index, we can't make a good
 *	prediction of the selectivity of these operators.
 *
 *	Note: the values used here may look unreasonably small.  Perhaps they
 *	are.  For now, we want to make sure that the optimizer will make use
 *	of a geometric index if one is available, so the selectivity had better
 *	be fairly small.
 *
 *	In general, GiST needs to search multiple subtrees in order to guarantee
 *	that all occurrences of the same key have been found.  Because of this,
 *	the estimated cost for scanning the index ought to be higher than the
 *	output selectivity would indicate.  gistcostestimate(), over in selfuncs.c,
 *	ought to be adjusted accordingly --- but until we can generate somewhat
 *	realistic numbers here, it hardly matters...
 */


/*
 * Selectivity for operators that depend on area, such as "overlap".
 */

Datum
areasel(PG_FUNCTION_ARGS)
{
	PG_RETURN_FLOAT8(0.005);
}

Datum
areajoinsel(PG_FUNCTION_ARGS)
{   
    
  PlannerInfo *root = (PlannerInfo *) PG_GETARG_POINTER(0);
    Oid         operator = PG_GETARG_OID(1);
    List       *args = (List *) PG_GETARG_POINTER(2);
    JoinType    jointype = (JoinType) PG_GETARG_INT16(3);
    SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) PG_GETARG_POINTER(4);
    Oid         collation = PG_GET_COLLATION();

    double      selec = 0.005;

    VariableStatData vardata1;
    VariableStatData vardata2;
    Oid         opfuncoid;
    AttStatsSlot sslot1;
    AttStatsSlot sslot2;
    int         nhist;
    int         nhist1;
    RangeBound *hist_lower1;
    RangeBound *hist_upper1;
    RangeBound *hist_lower2;
    RangeBound *hist_upper2;
    int         i;
    Form_pg_statistic stats1 = NULL;
    TypeCacheEntry *typcache = NULL;
    Form_pg_statistic stats2 = NULL;
    TypeCacheEntry *typcache1 = NULL;
    bool        join_is_reversed;
    bool        empty;
    double      hist_selec;

    get_join_variables(root, args, sjinfo,
                       &vardata1, &vardata2, &join_is_reversed);

    typcache = range_get_typcache(fcinfo, vardata1.vartype);
    opfuncoid = get_opcode(operator);

    memset(&sslot1, 0, sizeof(sslot1));

    /* Can't use the histogram with insecure range support functions */
    if (!statistic_proc_security_check(&vardata1, opfuncoid))
        PG_RETURN_FLOAT8((float8) selec);

    if (HeapTupleIsValid(vardata1.statsTuple))
    {
        stats1 = (Form_pg_statistic) GETSTRUCT(vardata1.statsTuple);
        /* Try to get fraction of empty ranges */
        if (!get_attstatsslot(&sslot1, vardata1.statsTuple,
                             STATISTIC_KIND_BOUNDS_HISTOGRAM,
                             InvalidOid, ATTSTATSSLOT_VALUES))
        {
            ReleaseVariableStats(vardata1);
            ReleaseVariableStats(vardata2);
            PG_RETURN_FLOAT8((float8) selec);
        }
    }

    nhist = sslot1.nvalues;
    hist_lower1 = (RangeBound *) palloc(sizeof(RangeBound) * nhist);
    hist_upper1 = (RangeBound *) palloc(sizeof(RangeBound) * nhist);
    for (i = 0; i < nhist; i++)
    {
        range_deserialize(typcache, DatumGetRangeTypeP(sslot1.values[i]),
                          &hist_lower1[i], &hist_upper1[i], &empty);
        /* The histogram should not contain any empty ranges */
        if (empty)
            elog(ERROR, "bounds histogram contains an empty range");
    }


/* for the 2nd variable */


    typcache1 = range_get_typcache(fcinfo, vardata2.vartype);
    opfuncoid = get_opcode(operator);

    memset(&sslot2, 0, sizeof(sslot2));

    /* Can't use the histogram with insecure range support functions */
    if (!statistic_proc_security_check(&vardata2, opfuncoid))
        PG_RETURN_FLOAT8((float8) selec);

    if (HeapTupleIsValid(vardata2.statsTuple))
    {
        stats2 = (Form_pg_statistic) GETSTRUCT(vardata2.statsTuple);
        /* Try to get fraction of empty ranges */
        if (!get_attstatsslot(&sslot2, vardata2.statsTuple,
                             STATISTIC_KIND_BOUNDS_HISTOGRAM,
                             InvalidOid, ATTSTATSSLOT_VALUES))
        {
            ReleaseVariableStats(vardata1);
            ReleaseVariableStats(vardata2);
            PG_RETURN_FLOAT8((float8) selec);
        }
    }

    nhist1 = sslot2.nvalues;
    hist_lower2 = (RangeBound *) palloc(sizeof(RangeBound) * nhist1);
    hist_upper2 = (RangeBound *) palloc(sizeof(RangeBound) * nhist1);
    for (i = 0; i < nhist1; i++)
    {
        range_deserialize(typcache1, DatumGetRangeTypeP(sslot2.values[i]),
                          &hist_lower2[i], &hist_upper2[i], &empty);
        /* The histogram should not contain any empty ranges */
        if (empty)
            elog(ERROR, "bounds histogram contains an empty range");
    }


/*********************** start the algorithm *****************************/


RangeBound maxlower;
RangeBound minupper;
int count=0;

if (hist_lower1[0].val>=hist_lower2[0].val){
    maxlower.val=hist_lower1[0].val;

    for (i=0;i<nhist1;i++)
    {
        if (hist_lower2[i].val<maxlower.val)
        {
            count++;
        }
    }
}
else
{
    maxlower.val=hist_lower2[0].val;
    for (i=0;i<nhist;i++)
    {
        if (hist_lower1[i].val<maxlower.val)
        {
            count++;
        }
    }
}

if (hist_upper1[nhist-1].val<=hist_upper2[nhist1-1].val){
    minupper.val=hist_upper1[nhist-1].val;

    for (i=0;i<nhist1;i++)
    {
        if (hist_upper2[i].val>minupper.val)
        {
            count++;
        }
    }

}
else
{
    minupper.val=hist_upper2[nhist1-1].val;
    for (i=0;i<nhist;i++)
    {
        if (hist_upper1[i].val>minupper.val)
        {
            count++;
        }
    }
}

printf("%d",count);
selec=((nhist+nhist1)-count)/(nhist+nhist1);

/*printf("Value of d = %lf\n",selec);*/

	
    fflush(stdout);

    pfree(hist_lower1);
    pfree(hist_upper1);

    free_attstatsslot(&sslot1);

    pfree(hist_lower2);
    pfree(hist_upper2);

    free_attstatsslot(&sslot2);

    ReleaseVariableStats(vardata1);
    ReleaseVariableStats(vardata2);

    CLAMP_PROBABILITY(selec);
    PG_RETURN_FLOAT8((float8) selec);
}

/*
 *	positionsel
 *
 * yHow likely is a box to be strictly left of (right of, above, below)
 * a given box?
 */

Datum
positionsel(PG_FUNCTION_ARGS)
{
	PG_RETURN_FLOAT8(0.1);
}

Datum
positionjoinsel(PG_FUNCTION_ARGS)
{
	PG_RETURN_FLOAT8(0.1);
}

/*
 *	contsel -- How likely is a box to contain (be contained by) a given box?
 *
 * This is a tighter constraint than "overlap", so produce a smaller
 * estimate than areasel does.
 */

Datum
contsel(PG_FUNCTION_ARGS)
{
	PG_RETURN_FLOAT8(0.001);
}

Datum
contjoinsel(PG_FUNCTION_ARGS)
{
	PG_RETURN_FLOAT8(0.001);
}
/*
 * Range Overlaps Join Selectivity.
 */




