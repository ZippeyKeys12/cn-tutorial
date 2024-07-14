struct int_bst {
    int value;
    struct int_bst* left;
    struct int_bst* right;
};

/*@
    datatype bst {
        BST_Leaf {},
        BST_Node { i32 value, datatype bst left, datatype bst right }
    }

    predicate (datatype bst) IntBST(pointer p) {
        if (is_null(p)) {
            return BST_Leaf {};
        } else {
            take n = Owned<struct int_bst>(p);

            take l = IntBST(n.left);
            assert (match l {
                BST_Leaf {} => { true }
                BST_Node {
                    value: v,
                    left: _,
                    right: _
                } => { v < n.value }
            });

            take r = IntBST(n.right);
            assert (match l {
                BST_Leaf {} => { true }
                BST_Node {
                    value: v,
                    left: _,
                    right: _
                } => { n.value < v}
            });
            return BST_Node { value: n.value, left: l, right: r };
        }
    }
@*/

extern struct int_bst* mallocIntBST();
/*@ spec mallocIntBST();
    requires
        true;
    ensures
        take T = Block<struct int_bst>(return);
@*/

struct int_bst* empty()
    /*@
    ensures
        take T = IntBST(return);
        T == BST_Leaf {};
    @*/
{
    return 0;
}

/*@
    function [rec] (datatype bst) insert(datatype bst tree, i32 to_insert) {
        match tree {
            BST_Leaf {} => {
                BST_Node {
                    value: to_insert,
                    left: BST_Leaf {},
                    right: BST_Leaf {}
                }
            }
            BST_Node {
                value: v,
                left: l,
                right: r
            } => {
                if (to_insert < v) {
                    BST_Node {
                        value: v,
                        left: insert(l, to_insert),
                        right: r
                    }
                } else {
                    if (v < to_insert) {
                        BST_Node {
                            value: v,
                            left: l,
                            right: insert(r, to_insert)
                        }
                    } else {
                        tree
                    }
                }
            }
        }
    }
@*/

struct int_bst* insert(struct int_bst* tree, int value)
    /*@
    requires
        take T1 = IntBST(tree);
    ensures
        take T2 = IntBST(return);
        T2 == insert(T1, value);
    @*/
{
    if (tree == 0) {
        struct int_bst* ret = mallocIntBST();
        ret->value = value;
        ret->left = 0;
        ret->right = 0;

        return ret;
    }

    if (value < tree->value) {
        tree->left = insert(tree->left, value);
    }
    else if (tree->value < value) {
        tree->right = insert(tree->right, value);
    }
    return tree;
}
