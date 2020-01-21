#include "nauty.h"

#include <limits.h>
#include <stdbool.h>

bool use_simple_lower_bound = true;
bool use_path_lower_bound = true;
bool use_only_child_symmetry_break = true;
bool use_nauty_symmetry_break = true;
bool use_domination_symmetry_break = true;
bool use_vertex_reordering = true;
bool up_option = false;
int decision_k = -1;

int *precalculated_simple_lb;
int *parent;
int *vtx_pos_on_path;  // used by path_lower_bound()
int m = 0;

//https://stackoverflow.com/a/10380191/3347737
#define PASTE_HELPER(a,b) a ## b
#define PASTE(a,b) PASTE_HELPER(a,b)

// If you use these macros, don't modify bitset while iterating over it!
#define FOR_EACH_IN_BITSET_HELPER(v, bitset, i, sw, x) \
           for (int i=0;i<m;i++) {setword sw=bitset[i]; while (sw) {int x; TAKEBIT(x, sw); int v=i*WORDSIZE+x;
#define FOR_EACH_IN_BITSET(v, bitset) \
           FOR_EACH_IN_BITSET_HELPER(v, bitset, PASTE(i,__LINE__), PASTE(sw,__LINE__), PASTE(x,__LINE__))
#define FOR_EACH_IN_BITSET_INTERSECTION_HELPER(v, bitset1, bitset2, i, sw, x) \
           for (int i=0;i<m;i++) {setword sw=bitset1[i] & bitset2[i]; while (sw) {int x; TAKEBIT(x, sw); int v=i*WORDSIZE+x;
#define FOR_EACH_IN_BITSET_INTERSECTION(v, bitset1, bitset2) \
           FOR_EACH_IN_BITSET_INTERSECTION_HELPER(v, bitset1, bitset2, PASTE(i,__LINE__), PASTE(sw,__LINE__), PASTE(x,__LINE__))
#define END_FOR_EACH_IN_BITSET }}

/* We have a free-list of bitsets */

struct Bitset
{
    struct Bitset *next;
    setword bitset[];
};

struct Bitset *bitset_free_list_head = NULL;

struct Bitset *get_Bitset()
{
    if (bitset_free_list_head == NULL) {
        struct Bitset *b = malloc(sizeof(struct Bitset) + m * sizeof(setword));
        if (b == NULL)
            exit(1);
        b->next = NULL;
        bitset_free_list_head = b;
    }
    struct Bitset *b = bitset_free_list_head;
    bitset_free_list_head = b->next;
    return b;
}

setword *get_bitset()
{
    return get_Bitset()->bitset;
}

setword *get_empty_bitset()
{
    setword *b = get_bitset();
    for (int i=0; i<m; i++)
        b[i] = 0;
    return b;
}

setword *get_copy_of_bitset(setword const *vv)
{
    setword *b = get_bitset();
    for (int i=0; i<m; i++)
        b[i] = vv[i];
    return b;
}

void free_Bitset(struct Bitset *b)
{
    b->next = bitset_free_list_head;
    bitset_free_list_head = b;
}

void free_bitset(setword *bitset)
{
    struct Bitset *b = (struct Bitset *)((char *) bitset - offsetof(struct Bitset, bitset));
    free_Bitset(b);
}

void free_Bitsets(struct Bitset *b)
{
    while (b) {
        struct Bitset *next_to_free = b->next;
        free_Bitset(b);
        b = next_to_free;
    }
}

void deallocate_Bitsets()
{
    while (bitset_free_list_head) {
        struct Bitset *next_to_free = bitset_free_list_head->next;
        free(bitset_free_list_head);
        bitset_free_list_head = next_to_free;
    }
}

/*************************************/

void clear_bitset(setword *vv)
{
    for (int i=0; i<m; i++)
        vv[i] = 0;
}

bool isempty(setword *vv)
{
    for (int i=0; i<m; i++)
        if (vv[i])
            return false;
    return true;
}

bool intersection_is_empty(setword *vv, setword *ww)
{
    for (int i=0; i<m; i++)
        if (vv[i] & ww[i])
            return false;
    return true;
}

int popcount(setword const *vv)
{
    int count = 0;
    for (int i=0; i<m; i++)
        count += POPCOUNT(vv[i]);
    return count;
}

int firstelement(setword const *vv)
{
    for (int i=0; i<m; i++)
        if (vv[i])
            return FIRSTBITNZ(vv[i]) + i * WORDSIZE;
    return -1;
}

int first_element_in_intersection(setword *vv, setword *ww)
{
    for (int i=0; i<m; i++)
        if (vv[i] & ww[i])
            return FIRSTBITNZ(vv[i] & ww[i]) + i * WORDSIZE;
    return -1;
}

// Returns a pointer to the first bitset in a linked list
struct Bitset *make_connected_components(setword *vv, graph *g)
{
    struct Bitset *retval = NULL;
    setword *visited = get_empty_bitset();
    setword *vv_in_prev_components = get_empty_bitset();
    setword *frontier = get_empty_bitset();
    for (int j=0; j<m; j++) {
        int x;
        while (WORDSIZE != (x = FIRSTBIT(vv[j] & ~visited[j]))) {
            int v = x + j * WORDSIZE;
            clear_bitset(frontier);
            ADDELEMENT(frontier, v);
            bool frontier_empty = false;
            while (!frontier_empty) {
                int u = firstelement(frontier);
                DELELEMENT(frontier, u);
                ADDELEMENT(visited, u);
                graph *graphrow = GRAPHROW(g, u, m);
                frontier_empty = true;
                for (int k=0; k<m; k++) {
                    frontier[k] |= graphrow[k] & ~visited[k] & vv[k];
                    frontier_empty &= frontier[k] == 0;
                }
            }

            struct Bitset *bitset = get_Bitset();
            bitset->next = retval;
            retval = bitset;
            setword *component = bitset->bitset;
            for (int k=0; k<m; k++)
                component[k] = visited[k] & ~vv_in_prev_components[k];

            for (int k=0; k<m; k++)
                vv_in_prev_components[k] |= visited[k];
        }
    }

    free_bitset(frontier);
    free_bitset(vv_in_prev_components);
    free_bitset(visited);
    return retval;
}

bool find_td(int path_len, int last_in_path, setword *vv, graph *g,
        int target_depth, int *orbits);

bool dominated(int v, setword const *component, graph *g)
{
    setword *v_and_w = get_empty_bitset();
    ADDELEMENT(v_and_w, v);
    FOR_EACH_IN_BITSET (w, component)
        if (w == v) {
            free_bitset(v_and_w);
            return false;
        }
        ADDELEMENT(v_and_w, w);
        bool v_has_extra = false;
        setword *row_v = GRAPHROW(g, v, m);
        setword *row_w = GRAPHROW(g, w, m);
        for (int i=0; i<m; i++) {
            v_has_extra |= (row_v[i] & ~row_w[i] & component[i] & ~v_and_w[i]) != 0;
        }
        if (!v_has_extra) {
            free_bitset(v_and_w);
            return true;
        }
        DELELEMENT(v_and_w, w);
    END_FOR_EACH_IN_BITSET
    free_bitset(v_and_w);
    return false;
}

bool find_td_of_connected_graph(int path_len, int last_in_path, setword const *component, graph *g,
        int target_depth, int *orbits, bool has_sibling)
{
    if (popcount(component) == 1) {
        parent[firstelement(component)] = last_in_path;
        return true;
    }

    bool only_child_rule_applies = use_only_child_symmetry_break && path_len > 0 && !has_sibling;

    FOR_EACH_IN_BITSET(v, component)
        if (only_child_rule_applies && v < last_in_path)
            continue;
        if (use_nauty_symmetry_break && path_len == 0 && orbits[v] < v && !has_sibling)
            continue;   // this symmetry break is only implemented for connected graphs for now
        if (use_domination_symmetry_break && dominated(v, component, g))
            continue;
        parent[v] = last_in_path;
        setword *descendant_vv = get_copy_of_bitset(component);
        DELELEMENT(descendant_vv, v);
        bool result = find_td(path_len + 1, v, descendant_vv, g, target_depth - 1, orbits);
        free_bitset(descendant_vv);
        if (result)
            return true;
    END_FOR_EACH_IN_BITSET
    return false;
}

int precalculate_simple_lower_bound(int vtx_count, int max_deg)
{
    if (max_deg == 0)
        return 0;
    if (vtx_count == 0)
        return 0;
    return 1 + precalculate_simple_lower_bound((vtx_count - 2 + max_deg) / max_deg, max_deg);
}

int simple_lower_bound(setword *component, graph *g)
{
    return precalculated_simple_lb[popcount(component)];
}

int path_lower_bound(setword *component, graph *g, int target)
{
    // an optimisation: find a path (or a cycle if we're lucky), and use it to compute a lower bound
    // on treedepth of the subgraph induced by the component

    // Avoid doing anything if even a Hamiltonian cycle wouldn't give a useful bound
    if (target >= 1 + 8*sizeof(unsigned) - __builtin_clz(popcount(component) - 1))
        return 0;

    setword *remaining = get_copy_of_bitset(component);
    int v0 = firstelement(remaining);
    DELELEMENT(remaining, v0);
    unsigned path_len = 1;
    vtx_pos_on_path[v0] = 0;
    for (int i=0; i<2; i++) {
        int pos = 0;
        int pos_step = i==0 ? 1 : -1;
        int v = v0;
        while (-1 != (v = first_element_in_intersection(remaining, GRAPHROW(g, v, m)))) {
            pos += pos_step;
            vtx_pos_on_path[v] = pos;
            ++path_len;
            DELELEMENT(remaining, v);
        }
    }
    setword *path_vv = get_bitset();
    for (int i=0; i<m; i++)
        path_vv[i] = component[i] ^ remaining[i];
    free_bitset(remaining);

    // Best bound uses the path lower bound...
    int best_bound = 8*sizeof(unsigned) - __builtin_clz(path_len);
    if (path_len > 2 && best_bound == target && target < 1 + 8*sizeof(unsigned) - __builtin_clz(path_len - 1)) {
        // ...but we also check if the path contains a cycle that gives a better bound
        FOR_EACH_IN_BITSET(v, path_vv)
            int pos_v = vtx_pos_on_path[v];
            FOR_EACH_IN_BITSET_INTERSECTION(w, path_vv, GRAPHROW(g, v, m))  // iterate over path-vertices that area adjacent to v
                int pos_w = vtx_pos_on_path[w];
                int pos_diff = pos_w > pos_v ? pos_w - pos_v : pos_v - pos_w;
                if (pos_diff == 1)
                    continue;     // v and w are adjacent, so not a cycle
                int cycle_len = pos_diff + 1;
                int cycle_bound = 1 + 8*sizeof(unsigned) - __builtin_clz(cycle_len - 1);
                if (cycle_bound > target) {
                    free_bitset(path_vv);
                    return cycle_bound;
                }
            END_FOR_EACH_IN_BITSET
        END_FOR_EACH_IN_BITSET
    }
    free_bitset(path_vv);
    return best_bound;
}

bool find_td(int path_len, int last_in_path, setword *vv, graph *g,
        int target_depth, int *orbits)
{
    if (target_depth == 0 && !isempty(vv))
        return false;

    struct Bitset *components = make_connected_components(vv, g);

    if (use_simple_lower_bound) {
        for (struct Bitset *component=components; component!=NULL; component=component->next) {
            if (simple_lower_bound(component->bitset, g) > target_depth) {
                free_Bitsets(components);
                return false;
            }
        }
    }

    if (use_path_lower_bound) {
        for (struct Bitset *component=components; component!=NULL; component=component->next) {
            if (path_lower_bound(component->bitset, g, target_depth) > target_depth) {
                free_Bitsets(components);
                return false;
            }
        }
    }

    for (struct Bitset *component=components; component!=NULL; component=component->next) {
        if (!find_td_of_connected_graph(path_len, last_in_path, component->bitset, g, target_depth,
                    orbits, components->next != NULL)) {
            free_Bitsets(components);
            return false;
        }
    }

    free_Bitsets(components);
    return true;
}

void verify_solution(graph *g, int n, int depth, bool exact_depth_expected,
        int *actual_depth)
{
    int number_of_endpoints_in_graph = 0;
    for (int i=0; i<n; i++) {
        number_of_endpoints_in_graph += popcount(GRAPHROW(g, i, m));
    }
    int number_of_edges_in_graph = number_of_endpoints_in_graph / 2;

    int max_depth_found = 0;
    int number_of_edges_satisfied = 0;
    int num_roots = 0;
    for (int i=0; i<n; i++) {
        int v = i;
        int path_len = 1;
        if (path_len > max_depth_found) {
            max_depth_found = path_len;
        }
        if (parent[v] == -1)
            ++num_roots;
        if (parent[v] == v) {
            printf("Invalid solution: vertex %d is its own parent\n", v);
            exit(1);
        }
        while (-1 != (v = parent[v])) {
            ++path_len;
            if (path_len > max_depth_found) {
                max_depth_found = path_len;
            }
            if (ISELEMENT(GRAPHROW(g, i, m), v)) {
                ++number_of_edges_satisfied;
            }
        }
    }
    if ((n==0) != (num_roots==0)) {
        // we should have no roots iff n==0
        printf("Invalid solution: %d roots\n", num_roots);
        exit(1);
    }
    if (max_depth_found > depth) {
        printf("Invalid solution: deeper than expected\n");
        exit(1);
    }
    if (exact_depth_expected && max_depth_found < depth) {
        printf("Invalid solution: not as deep than expected\n");
        exit(1);
    }
    if (number_of_edges_satisfied != number_of_edges_in_graph) {
        printf("Invalid solution: an edge in G does not have a corresponding ancestor-descendant relationship in T\n");
        exit(1);
    }
    *actual_depth = max_depth_found;
    printf("Solution verified.\n");
}

void show_forest_recursively(int root, int *children, int *start, int *len, int n)
{
    printf("%d", root + 1);    // display graph with 1-based numbering
    int *ch = children + start[root];
    for (int i=0; i<len[root]; i++) {
        int v  = ch[i];
        printf("(");
        show_forest_recursively(v, children, start, len, n);
        printf(")");
    }
}

void show_forest(int n)
{
    if (n == 0)
        return;

    int *children = malloc(n * sizeof *children);
    int *start = malloc(n * sizeof *start);   // start[v] is the position in children where the list of v's children begins
    int *len = malloc(n * sizeof *len);
    int *roots = malloc(n * sizeof *roots);
    int roots_len = 0;
    int cursor = 0;
    for (int i=0; i<n; i++) {
        if (parent[i] == -1)
            roots[roots_len++] = i;
        start[i] = cursor;
        for (int j=0; j<n; j++) {
            if (parent[j] == i) {
                children[cursor++] = j;
            }
        }
        len[i] = cursor - start[i];
    }
    for (int i=0; i<roots_len; i++) {
        if (i > 0)
            printf(" ");
        int root = roots[i];
        show_forest_recursively(root, children, start, len, n);
    }
    printf("\n");

    printf("Parents:");
    for (int i=0; i<n; i++)
        printf(" %d", parent[i] + 1);
    printf("\n");

    free(children);
    free(start);
    free(len);
    free(roots);
}

struct VtxInfo
{
    int v;
    int degree;
};

int cmp_deg_nonincreasing(const void *a, const void *b)
{
    const struct VtxInfo *vtx_info0 = a;
    const struct VtxInfo *vtx_info1 = b;
    if (vtx_info0->degree > vtx_info1->degree)
        return -1;
    if (vtx_info0->degree < vtx_info1->degree)
        return 1;
    if (vtx_info0->v < vtx_info1->v)
        return -1;
    if (vtx_info0->v > vtx_info1->v)
        return 1;
    return 0;
}

void find_order(graph *g, int n, int *vtx_order_sorted,
            int *vtx_order_sorted_inverse)
{
    struct VtxInfo *vtx_info = malloc(n * sizeof *vtx_info);
    for (int i=0; i<n; i++)
        vtx_info[i] = (struct VtxInfo) {i, popcount(GRAPHROW(g, i, m))};
    qsort(vtx_info, n, sizeof *vtx_info, cmp_deg_nonincreasing);
    for (int i=0; i<n; i++)
        vtx_order_sorted[i] = vtx_info[i].v;
    for (int i=0; i<n; i++)
        vtx_order_sorted_inverse[vtx_order_sorted[i]] = i;
    free(vtx_info);
}

int main(int argc, char *argv[])
{
    if (argc > 1) {
        for (int i=1; i<argc; i++) {
            if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
                printf("Find the treedepth of a graph.\n");
                printf("Command-line options:\n");
                printf("  --no-simple-lower-bound                don't use simple lower bound\n");
                printf("  --no-path-lower-bound                  don't use greed path lower bound\n");
                printf("  --no-only-child-symmetry-break         don't do symmetry breaking for nodes that have no siblings\n");
                printf("  --no-nauty                             don't use Nauty for symmetry breaking\n");
                printf("  --no-domination                        don't use domination symmetry breaking\n");
                printf("  --no-vertex-reordering                 don't reorder vertices by degree\n");
                printf("  --no-optimisations                     equivalent to using all of the other --no-... flags\n");
                printf("  --up                                   increment rather than decrement treedepth parameter\n");
                printf("  <k> (integer)                          solve the decision problem for depth k\n");
                exit(0);
            } else if (strcmp(argv[i], "--no-simple-lower-bound") == 0) {
                use_simple_lower_bound = false;
            } else if (strcmp(argv[i], "--no-path-lower-bound") == 0) {
                use_path_lower_bound = false;
            } else if (strcmp(argv[i], "--no-only-child-symmetry-break") == 0) {
                use_only_child_symmetry_break = false;
            } else if (strcmp(argv[i], "--no-nauty") == 0) {
                use_nauty_symmetry_break = false;
            } else if (strcmp(argv[i], "--no-domination") == 0) {
                use_domination_symmetry_break = false;
            } else if (strcmp(argv[i], "--no-vertex-reordering") == 0) {
                use_vertex_reordering = false;
            } else if (strcmp(argv[i], "--no-optimisations") == 0) {
                use_simple_lower_bound = false;
                use_path_lower_bound = false;
                use_only_child_symmetry_break = false;
                use_nauty_symmetry_break = false;
                use_domination_symmetry_break = false;
                use_vertex_reordering = false;
            } else if (strcmp(argv[i], "--up") == 0) {
                up_option = true;
            } else {
                decision_k = atoi(argv[i]);
            }
        }
    }

    char s[256];
    for (int i=0; i<2; i++)
        if(scanf("%s", s) != 1)
            exit(1);

    int n, edge_count;
    if (scanf("%d", &n) != 1)
        exit(1);
    precalculated_simple_lb = malloc((n + 1) * sizeof *precalculated_simple_lb);
    parent = malloc(n * sizeof *parent);
    vtx_pos_on_path = malloc(n * sizeof *vtx_pos_on_path);
    int *vtx_order_sorted = malloc(n * sizeof *vtx_order_sorted);
    int *vtx_order_sorted_inverse = malloc(n * sizeof *vtx_order_sorted_inverse);
    int *orbits = malloc(n * sizeof *orbits);

    m = SETWORDSNEEDED(n);
    if (scanf("%d", &edge_count) != 1)
        exit(1);

    graph *g = calloc(n * m, sizeof(graph));
    for (int i=0; i<edge_count; i++) {
        int v, w;
        if (scanf("%d %d", &v, &w) != 2)
            exit(1);
        if (v == w)
            continue;
        --v;
        --w;
        ADDONEEDGE(g, v, w, m);
    }

    int max_deg = 0;
    for (int i=0; i<n; i++) {
        int pc = popcount(GRAPHROW(g, i, m));
        if (pc > max_deg)
            max_deg = pc;
    }
    for (int i=0; i<=n; i++)
        precalculated_simple_lb[i] = precalculate_simple_lower_bound(i, max_deg);

    graph *reordered_g_ptr;
    if (use_vertex_reordering) {
        reordered_g_ptr = calloc(n * m, sizeof(graph));
        find_order(g, n, vtx_order_sorted, vtx_order_sorted_inverse);
        for (int v=0; v<n; v++) {
            FOR_EACH_IN_BITSET(w, GRAPHROW(g, v, m))
                int new_v = vtx_order_sorted_inverse[v];
                int new_w = vtx_order_sorted_inverse[w];
                ADDELEMENT(GRAPHROW(reordered_g_ptr, new_v, m), new_w);
            END_FOR_EACH_IN_BITSET
        }
    } else {
        reordered_g_ptr = g;
        for (int i=0; i<n; i++) {
            vtx_order_sorted[i] = i;
            vtx_order_sorted_inverse[i] = i;
        }
    }

    if (use_nauty_symmetry_break) {
        static DEFAULTOPTIONS_GRAPH(options);
        static statsblk stats;
        int *lab = malloc(n * sizeof *lab);
        int *ptn = malloc(n * sizeof *ptn);
        int workspace_sz = 120 * m;
        setword *workspace = malloc(workspace_sz * sizeof *workspace);
        nauty(reordered_g_ptr,lab,ptn,NULL,orbits,&options,&stats,workspace,workspace_sz,m,n,NULL);
        free(lab);
        free(ptn);
        free(workspace);
    }

    setword *vv = get_empty_bitset();
    for (int i=0; i<n; i++)
        ADDELEMENT(vv, i);

    int depth = -1;
    if (decision_k != -1) {
        bool result = find_td(0, -1, vv, reordered_g_ptr, decision_k, orbits);
        depth = result ? decision_k : -1;
    } else if (up_option) {
        int target_depth = 0;
        while (!find_td(0, -1, vv, reordered_g_ptr, target_depth, orbits)) {
            ++target_depth;
            printf("%d\n", target_depth);
        }
        depth = target_depth;
    } else if (n == 0) {
        depth = 0;
    } else {
        int target_depth = n;
        int *stored_parent = malloc(n * sizeof *stored_parent);
        while (find_td(0, -1, vv, reordered_g_ptr, target_depth, orbits)) {
            for (int i=0; i<n; i++)
                stored_parent[i] = parent[i];
            --target_depth;
            printf("%d\n", target_depth);
        }
        for (int i=0; i<n; i++)
            parent[i] = stored_parent[i];
        depth = target_depth + 1;
        free(stored_parent);
    }

    if (depth != -1) {
        int actual_depth = -1;  // only interesting for decision problem
        // smaller-than-requested depth is permitted for optimisation problem
        verify_solution(reordered_g_ptr, n, depth, decision_k==-1, &actual_depth);

        int *reordered_parent = malloc(n * sizeof *reordered_parent);
        for (int i=0; i<n; i++) {
            int p = parent[i];
            reordered_parent[vtx_order_sorted[i]] =
                    p==-1 ? -1 : vtx_order_sorted[p];
        }
        for (int i=0; i<n; i++)
            parent[i] = reordered_parent[i];
        free(reordered_parent);

        verify_solution(g, n, depth, decision_k==-1, &actual_depth);

        show_forest(n);

        if (decision_k == -1)
            printf("Depth %d\n", depth);
        else
            printf("A treedepth decomposition of depth %d was found (target %d)\n", actual_depth, decision_k);
//        printf("---------------------------------------\n");
//        printf("%d\n", actual_depth);
//        for (int i=0; i<n; i++)
//            printf("%d\n", parent[i] + 1);
    } else {
        printf("No treedepth decomposition of depth %d exists\n", decision_k);
    }
    if (reordered_g_ptr != g)
        free(reordered_g_ptr);
    free(g);
    free_bitset(vv);
    free(parent);
    free(precalculated_simple_lb);
    free(vtx_pos_on_path);
    free(vtx_order_sorted);
    free(vtx_order_sorted_inverse);
    free(orbits);
    deallocate_Bitsets();
}
