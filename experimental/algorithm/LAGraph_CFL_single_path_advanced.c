#define LG_FREE_WORK                                                                    \
    {                                                                                   \
        if (outputs_reachability != NULL) {                                             \
            for (size_t i = 0; i < symbols_amount; i++) {                               \
                GrB_free(&outputs_reachability[i]);                                     \
            }                                                                           \
        }                                                                               \
        LAGraph_Free((void **)&outputs_reachability, NULL);                             \
        LAGraph_Free((void **)&reachability_matrices, NULL);                            \
        LAGraph_Free((void **)&T, NULL);                                                \
        LAGraph_Free((void **)&t_empty_flags, NULL);                                    \
        LAGraph_Free((void **)&new_rules, NULL);                                        \
        LAGraph_Free((void **)&eps_rules, NULL);                                        \
        LAGraph_Free((void **)&term_rules, NULL);                                       \
        LAGraph_Free((void **)&bin_rules, NULL);                                       \
        GrB_free(&identity_matrix);                                                     \
        GrB_free(&v_diag);                                                              \
        GrB_free(&false_scalar);                                                        \
        GrB_free(&Theta);                                                               \
        GrB_free(&bottom_scalar);                                                       \
        GrB_free(&PathIndex_semiring);                                                  \
        GrB_free(&PathIndex_monoid);                                                    \
        GrB_free(&PathIndex_add);                                                       \
        GrB_free(&PathIndex_mult);                                                      \
        GrB_free(&PathIndex_set);                                                       \
        GrB_free(&IPathIndex_mult);                                                     \
        GrB_free(&IPathIndex_set);                                                      \
    }

#define LG_FREE_ALL                                                                     \
    {                                                                                   \
        LG_FREE_WORK;                                                                   \
        if (outputs_initialized) {                                                      \
            for (size_t i = 0; i < symbols_amount; i++) {                              \
                GrB_free(&outputs[i]);                                                  \
            }                                                                           \
        }                                                                               \
        if (path_index_type_created)                                                     \
            GrB_free(path_index_t);                                                      \
    }

#include "LG_internal.h"
#include <LAGraphX.h>

static void add_path_index_adv(PathIndex *z, const PathIndex *x, const PathIndex *y)
{
    if (x->height == 0 && x->middle == 0) {
        *z = *y;
    } else if (y->height == 0 && y->middle == 0) {
        *z = *x;
    } else if (x->height < y->height ||
               (x->height == y->height && x->middle <= y->middle)) {
        *z = *x;
    } else {
        *z = *y;
    }
}

static void mult_path_index_adv(
    PathIndex *z,
    const PathIndex *x, GrB_Index ix, GrB_Index jx,
    const PathIndex *y, GrB_Index iy, GrB_Index jy,
    const void *theta)
{
    if ((x->height == 0 && x->middle == 0) ||
        (y->height == 0 && y->middle == 0)) {
        z->height = 0;
        z->middle = 0;
    } else {
        z->middle = jx;
        z->height = (x->height > y->height ? x->height : y->height) + 1;
    }
}

static void set_path_index_adv(
    PathIndex *z,
    const PathIndex *x, GrB_Index ix, GrB_Index jx,
    const bool *edge_exist, GrB_Index i_edge, GrB_Index j_edge,
    const void *theta)
{
    if (*edge_exist) {
        z->middle = ix;
        z->height = 1;
    } else {
        z->middle = 0;
        z->height = 0;
    }
}

#define MULT_PATH_INDEX_ADV_DEFN                                                        \
    "void mult_path_index_adv(                                                         \n" \
    "    PathIndex *z,                                                                \n" \
    "    const PathIndex *x, GrB_Index ix, GrB_Index jx,                              \n" \
    "    const PathIndex *y, GrB_Index iy, GrB_Index jy,                              \n" \
    "    const void *theta)                                                           \n" \
    "{                                                                                \n" \
    "    if ((x->height == 0 && x->middle == 0) ||                                    \n" \
    "        (y->height == 0 && y->middle == 0)) {                                    \n" \
    "        z->height = 0;                                                           \n" \
    "        z->middle = 0;                                                           \n" \
    "    } else {                                                                     \n" \
    "        z->middle = jx;                                                          \n" \
    "        z->height = (x->height > y->height ? x->height : y->height) + 1;          \n" \
    "    }                                                                            \n" \
    "}"

#define SET_PATH_INDEX_ADV_DEFN                                                        \
    "void set_path_index_adv(                                                         \n" \
    "    PathIndex *z,                                                                \n" \
    "    const PathIndex *x, GrB_Index ix, GrB_Index jx,                              \n" \
    "    const bool *edge_exist, GrB_Index i_edge, GrB_Index j_edge,                  \n" \
    "    const void *theta)                                                           \n" \
    "{                                                                                \n" \
    "    if (*edge_exist) {                                                           \n" \
    "        z->height = 1;                                                           \n" \
    "        z->middle = ix;                                                          \n" \
    "    } else {                                                                     \n" \
    "        z->height = 0;                                                           \n" \
    "        z->middle = 0;                                                           \n" \
    "    }                                                                            \n" \
    "}"

GrB_Info LAGraph_CFL_single_path_adv(
    GrB_Matrix *outputs,
    GrB_Type *path_index_t,
    const GrB_Matrix *adj_matrices,
    size_t symbols_amount,
    const LAGraph_rule_EWCNF *rules,
    size_t rules_count,
    char *msg,
    int8_t optimizations)
{
    LG_CLEAR_MSG;

    GrB_Type PathIndex_type = NULL;
    GrB_BinaryOp PathIndex_add = NULL, PathIndex_mult = NULL;
    GrB_BinaryOp PathIndex_set = NULL;
    GrB_Monoid PathIndex_monoid = NULL;
    GxB_IndexBinaryOp IPathIndex_mult = NULL, IPathIndex_set = NULL;
    GrB_Semiring PathIndex_semiring = NULL;
    GrB_Scalar Theta = NULL, bottom_scalar = NULL, false_scalar = NULL;

    GrB_Matrix *T = NULL;
    GrB_Matrix *outputs_reachability = NULL, *reachability_matrices = NULL;
    GrB_Matrix identity_matrix = NULL;
    GrB_Vector v_diag = NULL;
    LAGraph_rule_EWCNF *new_rules = NULL;
    size_t new_rules_count = 0;
    size_t *eps_rules = NULL, eps_rules_count = 0;
    size_t *term_rules = NULL, term_rules_count = 0;
    size_t *bin_rules = NULL, bin_rules_count = 0;
    bool *t_empty_flags = NULL;
    bool outputs_initialized = false;
    bool path_index_type_created = false;

#if GxB_IMPLEMENTATION < GxB_VERSION(9, 4, 5)
    return GrB_NOT_IMPLEMENTED;
#else
    GrB_Index n = 0;

    LG_ASSERT_MSG(outputs != NULL, GrB_NULL_POINTER, "The outputs array cannot be null.");
    LG_ASSERT_MSG(path_index_t != NULL, GrB_NULL_POINTER,
                  "The PathIndex type handle cannot be null.");
    LG_ASSERT_MSG(adj_matrices != NULL, GrB_NULL_POINTER,
                  "The adjacency matrices array cannot be null.");
    LG_ASSERT_MSG(rules != NULL, GrB_NULL_POINTER, "The rules array cannot be null.");
    LG_ASSERT_MSG(symbols_amount > 0, GrB_INVALID_VALUE,
                  "The number of symbols must be greater than zero.");
    LG_ASSERT_MSG(rules_count > 0, GrB_INVALID_VALUE,
                  "The number of rules must be greater than zero.");
    LG_ASSERT_MSG(*path_index_t == NULL, GrB_INVALID_VALUE,
                  "The PathIndex type handle must be NULL on input.");

    for (size_t i = 0; i < symbols_amount; i++)
        outputs[i] = NULL;
    outputs_initialized = true;

    LG_TRY(LAGraph_Calloc((void **)&outputs_reachability, symbols_amount,
                          sizeof(GrB_Matrix), msg));
    LG_TRY(LAGraph_CFL_reachability_adv(outputs_reachability, adj_matrices,
                                        symbols_amount, rules, rules_count, msg,
                                        optimizations));

    LG_TRY(LAGraph_Calloc((void **)&reachability_matrices, symbols_amount,
                          sizeof(GrB_Matrix), msg));
    for (size_t i = 0; i < symbols_amount; i++) {
        reachability_matrices[i] = outputs_reachability[i] != NULL
                                       ? outputs_reachability[i]
                                       : adj_matrices[i];
        if (outputs_reachability[i] != NULL)
            GRB_TRY(GrB_set(outputs_reachability[i], GrB_ROWMAJOR,
                            GrB_STORAGE_ORIENTATION_HINT));
    }

    for (size_t i = 0; i < rules_count; i++) {
        new_rules_count += (rules[i].indexed_count == 0) ? 1 : rules[i].indexed_count;
    }

    LG_TRY(LAGraph_Calloc((void **)&new_rules, new_rules_count,
                          sizeof(LAGraph_rule_EWCNF), msg));
    size_t nr_idx = 0;
    for (size_t i = 0; i < rules_count; i++) {
        LAGraph_rule_EWCNF rule = rules[i];
        if (rule.indexed_count == 0) {
            new_rules[nr_idx++] = rule;
        } else {
            for (size_t rule_index = 0; rule_index < rule.indexed_count; rule_index++) {
                LAGraph_rule_EWCNF exploded_rule = rule;
                exploded_rule.indexed_count = 0;
                exploded_rule.indexed = 0;
                if (rule.nonterm != -1 && rule.indexed & LAGraph_EWNCF_INDEX_NONTERM) {
                    exploded_rule.nonterm = rule.nonterm + rule_index;
                }
                if (rule.prod_A != -1 && rule.indexed & LAGraph_EWNCF_INDEX_PROD_A) {
                    exploded_rule.prod_A = rule.prod_A + rule_index;
                }
                if (rule.prod_B != -1 && rule.indexed & LAGraph_EWNCF_INDEX_PROD_B) {
                    exploded_rule.prod_B = rule.prod_B + rule_index;
                }
                new_rules[nr_idx++] = exploded_rule;
            }
        }
    }

    LG_TRY(GxB_Type_new(path_index_t, sizeof(PathIndex), "PathIndex",
                        "typedef struct{size_t height;GrB_Index middle;}PathIndex;"));
    path_index_type_created = true;
    PathIndex_type = *path_index_t;

    GRB_TRY(GrB_Scalar_new(&Theta, GrB_BOOL));
    GRB_TRY(GrB_Scalar_setElement_BOOL(Theta, false));
    PathIndex bottom = {0, 0};
    GRB_TRY(GrB_Scalar_new(&bottom_scalar, PathIndex_type));
    GRB_TRY(GrB_Scalar_setElement_UDT(bottom_scalar, &bottom));
    GRB_TRY(GrB_Scalar_new(&false_scalar, GrB_BOOL));
    GRB_TRY(GrB_Scalar_setElement_BOOL(false_scalar, false));

    GRB_TRY(GrB_BinaryOp_new(&PathIndex_add, (void *)add_path_index_adv,
                             PathIndex_type, PathIndex_type, PathIndex_type));
    GRB_TRY(GrB_Monoid_new(&PathIndex_monoid, PathIndex_add, &bottom));
    GRB_TRY(GxB_IndexBinaryOp_new(&IPathIndex_mult, (void *)mult_path_index_adv,
                                  PathIndex_type, PathIndex_type, PathIndex_type,
                                  GrB_BOOL, "mult_path_index_adv",
                                  MULT_PATH_INDEX_ADV_DEFN));
    GRB_TRY(GxB_BinaryOp_new_IndexOp(&PathIndex_mult, IPathIndex_mult, Theta));
    GRB_TRY(GrB_Semiring_new(&PathIndex_semiring, PathIndex_monoid,
                             PathIndex_mult));
    GRB_TRY(GxB_IndexBinaryOp_new(&IPathIndex_set, (void *)set_path_index_adv,
                                  PathIndex_type, PathIndex_type, GrB_BOOL,
                                  GrB_BOOL, "set_path_index_adv",
                                  SET_PATH_INDEX_ADV_DEFN));
    GRB_TRY(GxB_BinaryOp_new_IndexOp(&PathIndex_set, IPathIndex_set, Theta));
    LG_TRY(GrB_Matrix_nrows(&n, adj_matrices[0]));
    LG_TRY(LAGraph_Calloc((void **)&T, symbols_amount, sizeof(GrB_Matrix), msg));
    LG_TRY(LAGraph_Calloc((void **)&t_empty_flags, symbols_amount, sizeof(bool), msg));
    for (size_t i = 0; i < symbols_amount; i++) {
        GRB_TRY(GrB_Matrix_new(&T[i], PathIndex_type, n, n));
        t_empty_flags[i] = true;
    }

    LG_TRY(LAGraph_Calloc((void **)&eps_rules, new_rules_count, sizeof(size_t), msg));
    LG_TRY(LAGraph_Calloc((void **)&term_rules, new_rules_count, sizeof(size_t), msg));
    LG_TRY(LAGraph_Calloc((void **)&bin_rules, new_rules_count, sizeof(size_t), msg));
    for (size_t i = 0; i < new_rules_count; i++) {
        LAGraph_rule_EWCNF rule = new_rules[i];
        if (rule.prod_A == -1 && rule.prod_B == -1)
            eps_rules[eps_rules_count++] = i;
        else if (rule.prod_A != -1 && rule.prod_B == -1)
            term_rules[term_rules_count++] = i;
        else if (rule.prod_A != -1 && rule.prod_B != -1)
            bin_rules[bin_rules_count++] = i;
    }

    for (size_t i = 0; i < symbols_amount; i++) {
        if (outputs_reachability[i] != NULL)
            continue;

        GrB_Index adj_matrix_nvals = 0;
        GRB_TRY(GrB_Matrix_nvals(&adj_matrix_nvals, adj_matrices[i]));
        if (adj_matrix_nvals == 0)
            continue;

        GRB_TRY(GxB_eWiseUnion(T[i], GrB_NULL, GrB_NULL, PathIndex_set,
                               T[i], bottom_scalar, adj_matrices[i],
                               false_scalar, GrB_NULL));
    }

    for (size_t i = 0; i < term_rules_count; i++) {
        LAGraph_rule_EWCNF term_rule = new_rules[term_rules[i]];
        GrB_Index adj_matrix_nvals = 0;
        GRB_TRY(GrB_Matrix_nvals(&adj_matrix_nvals,
                                 adj_matrices[term_rule.prod_A]));
        if (adj_matrix_nvals == 0)
            continue;

        GRB_TRY(GxB_eWiseUnion(T[term_rule.nonterm], GrB_NULL, GrB_NULL,
                               PathIndex_set, T[term_rule.nonterm], bottom_scalar,
                               adj_matrices[term_rule.prod_A], false_scalar,
                               GrB_NULL));
        t_empty_flags[term_rule.nonterm] = false;
    }

    if (eps_rules_count > 0) {
        GRB_TRY(GrB_Vector_new(&v_diag, GrB_BOOL, n));
        GRB_TRY(GrB_Vector_assign_BOOL(v_diag, GrB_NULL, GrB_NULL, true,
                                       GrB_ALL, n, GrB_NULL));
        GRB_TRY(GrB_Matrix_diag(&identity_matrix, v_diag, 0));
        GRB_TRY(GrB_free(&v_diag));

        for (size_t i = 0; i < eps_rules_count; i++) {
            LAGraph_rule_EWCNF eps_rule = new_rules[eps_rules[i]];
            GRB_TRY(GxB_eWiseUnion(T[eps_rule.nonterm], GrB_NULL, GrB_NULL,
                                   PathIndex_set, T[eps_rule.nonterm],
                                   bottom_scalar, identity_matrix, false_scalar,
                                   GrB_NULL));
            t_empty_flags[eps_rule.nonterm] = false;
        }
        GRB_TRY(GrB_free(&identity_matrix));
    }

    for (size_t i = 0; i < symbols_amount; i++) {
        GrB_Index nvals = 0;
        GRB_TRY(GrB_Matrix_nvals(&nvals, reachability_matrices[i]));
        if (nvals != 0)
            t_empty_flags[i] = false;
    }

    for (size_t i = 0; i < bin_rules_count; i++) {
        LAGraph_rule_EWCNF bin_rule = new_rules[bin_rules[i]];

        if (t_empty_flags[bin_rule.prod_A] || t_empty_flags[bin_rule.prod_B])
            continue;

        GrB_BinaryOp accum = t_empty_flags[bin_rule.nonterm]
                                 ? GrB_NULL
                                 : PathIndex_add;
        GRB_TRY(GrB_mxm(
            T[bin_rule.nonterm], GrB_NULL, accum, PathIndex_semiring,
            T[bin_rule.prod_A], T[bin_rule.prod_B], GrB_NULL));
        t_empty_flags[bin_rule.nonterm] = false;
    }

    for (size_t i = 0; i < symbols_amount; i++)
        GRB_TRY(GrB_Matrix_wait(T[i], GrB_MATERIALIZE));

    for (size_t i = 0; i < symbols_amount; i++) {
        if (outputs_reachability[i] == NULL)
            continue;
        outputs[i] = T[i];
    }

    LG_FREE_WORK;
    return GrB_SUCCESS;
#endif
}
