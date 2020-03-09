/***
 * cpddl
 * -------
 * Copyright (c)2016-2019 Daniel Fiser <danfis@danfis.cz>,
 * AI Center, Department of Computer Science,
 * Faculty of Electrical Engineering, Czech Technical University in Prague.
 * All rights reserved.
 *
 * This file is part of cpddl.
 *
 * Distributed under the OSI-approved BSD License (the "License");
 * see accompanying file BDS-LICENSE for details or see
 * <http://www.opensource.org/licenses/bsd-license.php>.
 *
 * This software is distributed WITHOUT ANY WARRANTY; without even the
 * implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the License for more information.
 */
#include <cstring>


static const char* root_type_cppdl = "__object_cpddl";
static const char* eq_name_cppdl = "__equals_cpddl";


/////////////////////////////////// COPIED FROM CPDDL/src/obj.c
struct obj_key {
    pddl_obj_id_t obj_id;
    const char *name;
    uint32_t hash;
    bor_list_t htable;
};
typedef struct obj_key obj_key_t;

static bor_htable_key_t objHash(const bor_list_t *key, void *_)
{
    const obj_key_t *obj = bor_container_of(key, obj_key_t, htable);
    return obj->hash;
}

static int objEq(const bor_list_t *key1, const bor_list_t *key2, void *_)
{
    const obj_key_t *obj1 = bor_container_of(key1, obj_key_t, htable);
    const obj_key_t *obj2 = bor_container_of(key2, obj_key_t, htable);
    return strcmp(obj1->name, obj2->name) == 0;
}

static void addEqPredicate(pddl_preds_t *ps)
{
    pddl_pred_t *p;

    p = pddlPredsAdd(ps);
    p->name = BOR_STRDUP(eq_name_cppdl);
    p->param_size = 2;
    p->param = BOR_CALLOC_ARR(int, 2);
    ps->eq_pred = ps->pred_size - 1;
}
/////////////////////////////////// COPIED FROM CPDDL/src/obj.c

/////////////////////////////////// COPIED FROM CPDDL/src/cond.c
#define condNew(CTYPE, TYPE) \
    (CTYPE *)_condNew(sizeof(CTYPE), TYPE)

static pddl_cond_t *_condNew(int size, unsigned type)
{
    pddl_cond_t *c;

    c = (pddl_cond_t*)BOR_MALLOC(size);
    bzero(c, size);
    c->type = type;
    borListInit(&c->conn);
    return c;
}

static pddl_cond_part_t *condPartNew(int type)
{
    pddl_cond_part_t *p;
    p = condNew(pddl_cond_part_t, type);
    borListInit(&p->part);
    return p;
}

static pddl_cond_atom_t *condAtomNew(void)
{
    return condNew(pddl_cond_atom_t, PDDL_COND_ATOM);
}

static void condPartAdd(pddl_cond_part_t *p, pddl_cond_t *add)
{
    borListInit(&add->conn);
    borListAppend(&p->part, &add->conn);
}

/////////////////////////////////// COPIED FROM CPDDL/src/cond.c


