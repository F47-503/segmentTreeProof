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
    trait Transform<U(!new), T(!new)> {
        var monoid: AbstractMonoid<T>
        function method identity(): U
        function method apply(elem: U, res: T): T
        function method compose(elem1: U, elem2: U): U
        predicate hasIdentity() {
            forall x: T :: apply(identity(), x) == x
        } 
        predicate isComposeAssociative() {
            forall x: U, y: U, z: T :: apply(compose(x, y), z) == apply(x, apply(y, z))
        }
        predicate isDustrubutive() 
            reads this
        {
            forall x: U, y: T, z: T :: apply(x, monoid.op(y, z)) == monoid.op(apply(x, y), apply(x, z))
        }
        predicate validTransform() 
            reads this
        {
            isComposeAssociative() && isDustrubutive() && hasIdentity()
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

function maxInt(left: int, right: int): int 
{
    if left < right then right else left
}


function minInt(left: int, right: int): int 
{
    if left > right then right else left
}

predicate validTreeValues<T(!new)>(tree: SegmentTree<T>, arr: array<T>, monoid: Monoid.AbstractMonoid<T>)
    reads arr
    requires monoid.validMonoid()
    requires 0 <= boundaries(tree).0 <= boundaries(tree).1 < arr.Length
    requires validTree(tree)
{
    var (l, r) := boundaries(tree);
    match tree {
        case Leaf(l, val) => arr[l] == val
        case Node(l, m, r, left, right, val) => 
            validTreeValues(left, arr, monoid) && 
            validTreeValues(right, arr, monoid) &&
            val == straightQuery(arr, l, r, monoid)
    }
}

function method buildTree<T(!new)>(arr: array<T>, l: int, r: int, monoid: Monoid.AbstractMonoid<T>): (res: SegmentTree<T>)
    reads arr
    requires 0 <= l <= r < arr.Length
    requires monoid.validMonoid()
    ensures boundaries(res) == (l, r)
    ensures getValue(res) == straightQuery(arr, l, r, monoid)
    ensures validTree(res)
    ensures validTreeValues(res, arr, monoid)
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

    
lemma validTreeValuesRange<T(!new)>(tree: SegmentTree<T>, arr: array<T>, monoid: Monoid.AbstractMonoid<T>)
    requires 0 <= boundaries(tree).0  < arr.Length
    requires 0 <= boundaries(tree).1  < arr.Length
    requires monoid.validMonoid()
    requires validTree(tree)
    requires validTreeValues(tree, arr, monoid)
    decreases boundaries(tree).1 - boundaries(tree).0
    ensures straightQuery(arr, boundaries(tree).0, boundaries(tree).1, monoid) == getValue(tree)
    ensures match tree {
        case Leaf(x, val) => true
        case Node(l, m, r, left, right, val) => monoid.op(getValue(left), getValue(right)) == val
    }
{
    match tree {
        case Leaf(x, val) => assert true;
        case Node(l, m, r, left, right, val) => 
            validTreeValuesRange(left, arr, monoid);
            assert getValue(left) == straightQuery(arr, boundaries(left).0, boundaries(left).1, monoid);
            validTreeValuesRange(right, arr, monoid);
            assert getValue(right) == straightQuery(arr, boundaries(right).0, boundaries(right).1, monoid);
            associativeQuery(arr, l, m, r, monoid);
            assert monoid.op(getValue(left), getValue(right)) == val;
    }
}

lemma equalArraysEqualQueries<T(!new)>(arr1: array<T>, arr2: array<T>, l: int, r: int, monoid: Monoid.AbstractMonoid<T>) 
    requires arr1.Length == arr2.Length
    requires forall i :: 0 <= i < arr1.Length ==> arr1[i] == arr2[i]
    requires monoid.validMonoid()
    requires 0 <= l <= arr1.Length && 0 <= r < arr2.Length
    ensures straightQuery(arr1, l, r, monoid) == straightQuery(arr2, l, r, monoid)
    decreases r - l
{
    if (l > r) {
        return;
    }
    assert arr1[l] == arr2[l];
    equalArraysEqualQueries(arr1, arr2, l + 1, r, monoid);
}

lemma equalArraysEqualTrees<T(!new)>(tree: SegmentTree<T>, arr1: array<T>, arr2: array<T>, monoid: Monoid.AbstractMonoid<T>) 
    requires arr1.Length == arr2.Length
    requires forall i :: 0 <= i < arr1.Length ==> arr1[i] == arr2[i]
    requires monoid.validMonoid()
    requires 0 <= boundaries(tree).0 <= boundaries(tree).1 < arr1.Length
    requires validTree(tree)
    requires validTreeValues(tree, arr1, monoid)
    ensures validTreeValues(tree, arr2, monoid)
    decreases tree
{
    var (l, r) := boundaries(tree);
    match tree {
        case Leaf(l, val) => assert arr2[l] == val;
        case Node(l, m, r, left, right, val) => 
            equalArraysEqualTrees(left, arr1, arr2, monoid);
            equalArraysEqualTrees(right, arr1, arr2, monoid);
            equalArraysEqualQueries(arr1, arr2, l, r, monoid);
    }
}

lemma splitSegmentQuery<T(!new)>(arr: array<T>, l: int, m: int, r: int, l1: int, r1: int, monoid: Monoid.AbstractMonoid<T>) 
    requires monoid.validMonoid()
    requires 0 <= l <= m <= r < arr.Length
    requires 0 <= l1 <= r1 < arr.Length
    ensures straightQuery(arr, maxInt(l, l1), minInt(r, r1), monoid) == 
        monoid.op(straightQuery(arr, maxInt(l, l1), minInt(m, r1), monoid), straightQuery(arr, maxInt(m + 1, l1), minInt(r, r1), monoid))
{
    if m < l1 {
        assert straightQuery(arr, maxInt(m + 1, l1), minInt(r, r1), monoid) == straightQuery(arr, l1, minInt(r, r1), monoid);
        assert straightQuery(arr, maxInt(l, l1), minInt(m, r1), monoid) == straightQuery(arr, l1, m, monoid) == monoid.identity();
        assert straightQuery(arr, l1, minInt(r, r1), monoid) == monoid.op(straightQuery(arr, maxInt(l, l1), minInt(m, r1), monoid), straightQuery(arr, maxInt(m + 1, l1), minInt(r, r1), monoid));
        assert straightQuery(arr, maxInt(l, l1), minInt(r, r1), monoid) == 
            monoid.op(straightQuery(arr, maxInt(l, l1), minInt(m, r1), monoid), straightQuery(arr, maxInt(m + 1, l1), minInt(r, r1), monoid));
        return;
    }
    if (m > r1) {
        assert straightQuery(arr, maxInt(l, l1), minInt(r, r1), monoid) == 
        monoid.op(straightQuery(arr, maxInt(l, l1), minInt(m, r1), monoid), straightQuery(arr, maxInt(m + 1, l1), minInt(r, r1), monoid));
        return;
    }
    associativeQuery(arr, maxInt(l1, l), m, minInt(r1, r), monoid);
}

predicate equalStructures<T, U>(tree1: SegmentTree<T>, tree2: SegmentTree<U>) 
{
    validTree(tree1) && 
    validTree(tree2) &&
    boundaries(tree1) == boundaries(tree2) &&
    match tree1 {
        case Node(l1, m1, r1, left1, right1, val1) => match tree2 {
            case Node(l2, m2, r2, left2, right2, val2) => equalStructures(left1, left2) && equalStructures(right1, right2)
            case Leaf(_,_) => false
        }
        case Leaf(x1, val1) => match tree2 {
            case Node(_, _, _, _, _, _) => false
            case Leaf(x2, val2) => x1 == x2
        }
    }
}

class SegmentTreeWrapper<T(!new)>
{
    var elemsInit: array<T>
    ghost var elems: array<T>
    var tree: SegmentTree<T>
    var monoid: Monoid.AbstractMonoid<T>

    predicate validStructure() 
        reads this
    {
        elems.Length == elemsInit.Length
    }

    predicate validSubtree(subTree: SegmentTree<T>)
        reads this
        reads elems
    {
        monoid.validMonoid() && validTree(subTree) && boundaries(subTree).0 >= 0 && boundaries(subTree).1 < elems.Length && validTreeValues(subTree, elems, monoid)
    }

    predicate fullTree() 
        reads this
    {
        boundaries(tree) == (0, elems.Length - 1)
    }

    method buildTreeInner()
        modifies this
        requires validStructure()
        requires monoid.validMonoid()
        requires elems.Length > 0
        requires forall i :: 0 <= i < elems.Length ==> elems[i] == elemsInit[i]
        ensures validSubtree(tree)
        ensures fullTree()    
    {
        var res := buildTree(elemsInit, 0, elemsInit.Length - 1, monoid);
        tree := res;
        equalArraysEqualTrees(tree, elemsInit, elems, monoid);
    }

    constructor(arr: array<T>, m: Monoid.AbstractMonoid<T>) 
        requires m.validMonoid()
        requires arr.Length > 0
        ensures monoid.validMonoid()
        ensures elems.Length == arr.Length == elemsInit.Length
    {
        elems := arr;
        elemsInit := arr;
        monoid := m;
        tree := Leaf(0, m.identity());
    }

    function method innerQuery(subTree:SegmentTree<T>, l: int, r: int): (res: T)
        reads elems
        reads this
        requires validSubtree(subTree)
        requires 0 <= l <= r < elems.Length
        requires 0 <= boundaries(subTree).0 < elems.Length
        requires 0 <= boundaries(subTree).1 < elems.Length
        ensures res == straightQuery(elems, maxInt(boundaries(subTree).0, l), minInt(boundaries(subTree).1, r), monoid)
        decreases subTree
    {
        var (leftPoint, rightPoint) := boundaries(subTree);
        if (r < leftPoint || l > rightPoint) 
        then assert monoid.identity() == straightQuery(elems, maxInt(leftPoint, l), minInt(rightPoint, r), monoid); monoid.identity()
        else if (l <= leftPoint <= rightPoint <= r) 
            then 
            assert straightQuery(elems, maxInt(l, leftPoint), minInt(r, rightPoint), monoid) == 
                straightQuery(elems, leftPoint, rightPoint, monoid);
            getValue(subTree)
            else match subTree {
                case Node(leftPoint, m, rightPoint, left, right, value) =>
                    splitSegmentQuery(elems, leftPoint, m, rightPoint, l, r, monoid);
                    assert straightQuery(elems, maxInt(l, leftPoint), minInt(r, rightPoint), monoid) == 
                        monoid.op(straightQuery(elems, maxInt(leftPoint, l), minInt(m, r), monoid), straightQuery(elems, maxInt(m + 1, l), minInt(rightPoint, r), monoid));
                    monoid.op(innerQuery(left, l, r), innerQuery(right, l, r))
                case Leaf(_, val) => assert leftPoint == rightPoint; val
            }
    }

    method query(l: int, r: int) returns (res: T)
        requires 0 <= l < elems.Length
        requires 0 <= r < elems.Length
        requires validSubtree(tree)
        requires fullTree()
        ensures res == straightQuery(elems, l, r, monoid)
    {
        if (l > r) {
            return monoid.identity();
        }
        assert boundaries(tree) == (0, elems.Length - 1);
        return innerQuery(tree, l, r);
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