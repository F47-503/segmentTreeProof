module Monoid {
    trait AbstractMonoid<T(!new)> {
        function method op(x: T, y: T): T
        function method identity(): T
            reads {}
        predicate isAssociative()
        {
            forall x, y, z :: op(op(x, y), z) == op(x, op(y, z))
        }

        predicate hasIdentity()
        {
            forall x :: op(identity(), x) == x && op(x, identity()) == x
        }

        predicate identityIdempotent()
        {
            identity() == op(identity(), identity())
        }

        predicate validMonoid()
        {
            isAssociative() &&
            hasIdentity() &&
            identityIdempotent()
        }
    } 

    class AddMonoid extends AbstractMonoid<int> {
        function method op(x: int, y: int): int
        {
            x + y
        }
        function method identity(): int
        reads {}
        {
            0
        }

        lemma valid()
        ensures validMonoid()
        {
        }
        constructor() {
        }
    }
    function method inf(): int {
        100
    }
    type BoundedInt = x: int | x <= inf()
    class MinMonoid extends AbstractMonoid<BoundedInt> {
        function method op(x: BoundedInt, y: BoundedInt): BoundedInt
        {
            if x < y then x else y
        }
        
        function method identity(): BoundedInt
        reads {}
        {
        inf()
        }

        lemma valid()
            ensures validMonoid()
        {
        }

        constructor() {
        }
    }

}
datatype SegmentTree<T> =
    Leaf(m: int, value: T)
    | Node(l: int, m: int, r: int, left: SegmentTree, right: SegmentTree, value: T)

predicate validTree(st: SegmentTree)
    decreases st
{
    match st
    {
        case Leaf(_, _) =>
            true

        case Node(ll, mm, rr, left, right, _) =>
            ll <= mm < rr
            && validTree(left)
            && validTree(right)
            && (match left {
                case Leaf(x, _) =>
                    x == ll && x == mm
                case Node(l2, m2, r2, _, _, _) =>
                    l2 == ll && r2 == mm
                })
            && (match right {
                case Leaf(x, _) =>
                    x == rr && x == mm + 1
                case Node(l2, m2, r2, _, _, _) =>
                    l2 == mm + 1 && r2 == rr
                })
    }
}

predicate validTreeValues<T(!new)>(tree: SegmentTree<T>, arr: array<T>, l: int, r: int, monoid: Monoid.AbstractMonoid<T>)
    reads arr
    requires 0 <= l <= r < arr.Length
    requires validTree(tree)
    requires boundaries(tree) == (l, r) 
{
    match tree {
        case Leaf(l, val) => arr[l] == val
        case Node(l, m, r, left, right, val) => 
            validTreeValues(left, arr, l, m, monoid) && 
            validTreeValues(right, arr, m + 1, r, monoid) &&
            val == monoid.op(getValue(left), getValue(right))
    }
}

function method boundaries(tree: SegmentTree): (int, int)
{
    match tree {
        case Node(l, _, r, _, _, _) => (l, r)
        case Leaf(x, _) => (x, x)
    }
}


function method getValue<T>(tree: SegmentTree<T>): T
{
    match tree {
        case Node(_, _, _, _, _, val) => val
        case Leaf(_, val) => val
    }
}

function method mergeTrees<T>(left: SegmentTree<T>, right: SegmentTree<T>, merge: (T, T) -> T): (res: SegmentTree<T>)
    requires validTree(left)
    requires validTree(right)
    requires boundaries(left).1 + 1 == boundaries(right).0
    ensures validTree(res)
    ensures match res {
        case Node(_, _, _, leftRes, rightRes, _) =>
            left == left && right == right
        case Leaf(_, _) => false
    }
    ensures getValue(res) == merge(getValue(left), getValue(right))
{
    Node(boundaries(left).0, boundaries(left).1, boundaries(right).1, left, right, merge(getValue(left), getValue(right)))
}

function method buildTree<T(!new)>(arr: array<T>, l: int, r: int, monoid: Monoid.AbstractMonoid<T>): (res: SegmentTree<T>)
    reads arr
    requires 0 <= l <= r < arr.Length
    requires monoid.validMonoid()
    ensures boundaries(res) == (l, r)
    ensures getValue(res) == straightQuery(arr, l, r, monoid)
    ensures validTree(res)
    ensures validTreeValues(res, arr, l, r, monoid)
    decreases r - l
{
    if l == r 
    then Leaf(l, arr[l]) 
    else (associativeQuery(arr, l, ((l + r) / 2), r, monoid); 
    mergeTrees(
        buildTree(arr, l, (l + r) / 2, monoid), 
        buildTree(arr, (l + r) / 2 + 1, r, monoid), monoid.op))
}

function straightQuery<T(!new)>(elems: array<T>, l: int, r: int, monoid: Monoid.AbstractMonoid<T>): (res: T) 
    reads elems
    requires 0 <= l <= elems.Length && 0 <= r < elems.Length
    requires monoid.hasIdentity()
    ensures r == l ==> res == elems[l]
    ensures r < l ==> res == monoid.identity()
    decreases r - l
{
    if l > r then monoid.identity() else monoid.op(elems[l], straightQuery(elems, l + 1, r, monoid))
}

lemma associativeQuery<T(!new)>(elems: array<T>, l: int, m: int, r: int, monoid: Monoid.AbstractMonoid<T>) 
    requires 0 <= l <= m <= r < elems.Length
    requires monoid.validMonoid()
    ensures straightQuery(elems, l, r, monoid) == monoid.op(straightQuery(elems, l, m, monoid), straightQuery(elems, m + 1, r, monoid))
    decreases r - l
{
    if (r == m) {
        assert straightQuery(elems, l, r, monoid) == monoid.op(straightQuery(elems, l, m, monoid), straightQuery(elems, m + 1, r, monoid));
        return;
    }
    assert straightQuery(elems, l, r, monoid) == monoid.op(straightQuery(elems, l, m, monoid), straightQuery(elems, m + 1, r, monoid));
}

class SegmentTreeWrapper<T(!new)>
{
    var elems: array<T>
    var tree: SegmentTree<T>
    var monoid: Monoid.AbstractMonoid<T>

    constructor(arr: array<T>, m: Monoid.AbstractMonoid<T>) 
        requires m.validMonoid()
        requires arr.Length > 0
        ensures monoid.validMonoid()
        ensures elems.Length == arr.Length
        ensures validTree(tree)
        ensures boundaries(tree) == (0, elems.Length - 1)
        ensures validTreeValues(tree, elems, 0, elems.Length - 1, monoid)
    {
        elems := arr;
        var mon := m;
        tree := buildTree(arr, 0, arr.Length - 1, mon);
        monoid := mon;
    }
}

method Main() {
    var addMonoidInstance := new Monoid.AddMonoid();
    var minMonoidInstance := new Monoid.MinMonoid();
    var minMonoidSt := new Monoid.MinMonoid();
    assert minMonoidSt.validMonoid();
    print addMonoidInstance.op(3, 13), " ";
    print addMonoidInstance.identity(), " ";
    print minMonoidInstance.op(3, 13), " ";
    print minMonoidInstance.identity(), " ";
    assert addMonoidInstance.validMonoid();    
}