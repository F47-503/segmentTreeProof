// this module supplies us with interface for monoid and some potential instances of monoids
module Monoid {
    trait AbstractMonoid<T(!new)> {
        // operation in monoid
        function method op(x: T, y: T): T
        // monoid neutral element
        function method identity(): T
            reads {}
        // monoid is associative 
        predicate isAssociative()
        {
            forall x, y, z :: op(op(x, y), z) == op(x, op(y, z))
        }
        // neutral element properties
        predicate hasIdentity()
        {
            forall x :: op(identity(), x) == x && op(x, identity()) == x
        }
        // we would normally use both in requirements
        predicate validMonoid()
        {
            isAssociative() &&
            hasIdentity()
        }
    } 
    // monoid on integers with + operation
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

        constructor() {
        }
    }
    // normally it is hard to define "the biggest integer", so we will create a type for constant 100
    function method inf(): int {
        100
    }
    type BoundedInt = x: int | x <= inf()
    // on bounded integers, we can define monoid with min operation
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

        constructor() {
        }
    }
}

// functional style tree on segments
datatype SegmentTree<T> =
    Leaf(m: int, value: T)
    | Node(l: int, m: int, r: int, left: SegmentTree, right: SegmentTree, value: T)

// predicate for validity of segments inside a segment tree. Defined recursively:
// If leaf, it is valid. Otherwise, children should be valid and match boundaries of original segment.
// Also their segments should be tangent at (m, m + 1)
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


// simple function to extract boundaries of the root for the tree
function method boundaries(tree: SegmentTree): (int, int)
{
    match tree {
        case Node(l, _, r, _, _, _) => (l, r)
        case Leaf(x, _) => (x, x)
    }
}

// simple function to extract value of the root for the tree 
function method getValue<T>(tree: SegmentTree<T>): T
{
    match tree {
        case Node(_, _, _, _, _, val) => val
        case Leaf(_, val) => val
    }
}

function method treeHeight<T>(tree: SegmentTree<T>): (res: int)
    requires validTree(tree)
    ensures res >= 0
{
    match tree {
        case Leaf(_, _) => 0
        case Node(_, _, _, left, right, _) => maxInt(treeHeight(left), treeHeight(right)) + 1
    }
}

// function for merging two segment trees at new root, We also need a lambda to calculate value at new root
function method mergeTrees<T>(left: SegmentTree<T>, right: SegmentTree<T>, merge: (T, T) -> T): (res: SegmentTree<T>)
    // both trees should have valid structure
    requires validTree(left)
    requires validTree(right)
    // their root segments should match
    requires boundaries(left).1 + 1 == boundaries(right).0
    // resulting tree should have valid structure
    ensures validTree(res)
    // children should be left and right, result cannot be a leaf
    ensures match res {
        case Node(_, _, _, leftRes, rightRes, _) =>
            left == left && right == right
        case Leaf(_, _) => false
    }
    // root value is correct
    ensures getValue(res) == merge(getValue(left), getValue(right))
    ensures treeHeight(res) == maxInt(treeHeight(left), treeHeight(right)) + 1;
{
    Node(boundaries(left).0, boundaries(left).1, boundaries(right).1, left, right, merge(getValue(left), getValue(right)))
}


// function for calculating maximum of two integers
function method maxInt(left: int, right: int): (res: int) 
    ensures res >= left && res >= right
    ensures res == left || res == right
{
    if left < right then right else left
}



// function for calculating minimum of two integers
function method minInt(left: int, right: int): (res: int) 
    ensures res <= left && res <= right
    ensures res == left || res == right{
    if left > right then right else left
}

// function which calculates a fold on subarray from l to r using monoid operation
function straightQuery<T(!new)>(elems: array<T>, l: int, r: int, monoid: Monoid.AbstractMonoid<T>): (res: T) 
    reads elems
    // valid bounds for l and r
    requires 0 <= l && 0 <= r < elems.Length
    // we return neutral if fold is empty
    requires monoid.hasIdentity()
    // two corner cases
    ensures r < l ==> res == monoid.identity()
    ensures r == l ==> res == elems[l]
    decreases r - l
{
    if l > r then monoid.identity() else monoid.op(elems[l], straightQuery(elems, l + 1, r, monoid))
}

// lemma: fold on tangent segments is fold on their union for associative opration
lemma associativeQuery<T(!new)>(arr: array<T>, l: int, m: int, r: int, monoid: Monoid.AbstractMonoid<T>) 
    // we will use only for these l, m, r
    requires 0 <= l <= m <= r < arr.Length
    requires monoid.validMonoid()
    ensures straightQuery(arr, l, r, monoid) == monoid.op(straightQuery(arr, l, m, monoid), straightQuery(arr, m + 1, r, monoid))
    decreases r - l
{
    if (r == m) {
        return;
    }
    assert straightQuery(arr, l, r, monoid) == monoid.op(straightQuery(arr, l, m, monoid), straightQuery(arr, m + 1, r, monoid));
}

// check that values in segment tree correspond to the actual folds on subarrays
predicate validTreeValues<T(!new)>(tree: SegmentTree<T>, arr: array<T>, monoid: Monoid.AbstractMonoid<T>)
    reads arr
    // monoid should be valid
    requires monoid.validMonoid()
    // tree should lie inside allowed segment
    requires 0 <= boundaries(tree).0 <= boundaries(tree).1 < arr.Length
    // tree should be valid
    requires validTree(tree)
{
    var (l, r) := boundaries(tree);
    match tree {
        // if leaf, fold is just element value
        case Leaf(l, val) => arr[l] == val
        // otherwise children should be ok and root value should be ok
        case Node(l, m, r, left, right, val) => 
            validTreeValues(left, arr, monoid) && 
            validTreeValues(right, arr, monoid) &&
            val == straightQuery(arr, l, r, monoid)
    }
}

// function that returns a valid segment tree with valid  values on subarray l, r of array using monoid operation
function method buildTree<T(!new)>(arr: array<T>, l: int, r: int, monoid: Monoid.AbstractMonoid<T>): (res: SegmentTree<T>)
    reads arr
    // valid subarray
    requires 0 <= l <= r < arr.Length
    // without associativity it is just incorrect
    requires monoid.validMonoid()
    // correct root value and boundaries
    ensures boundaries(res) == (l, r)
    ensures getValue(res) == straightQuery(arr, l, r, monoid)
    // correct structure and correct values in all tree
    ensures validTree(res)
    ensures validTreeValues(res, arr, monoid)
    ensures balancedTree(res)
    decreases r - l
{
    if l == r 
    then 
        assert 2 * (r - l + 1) > 1;
        Leaf(l, arr[l]) 
    else 
        // apply lemma to get that the value in root  is correct
        (associativeQuery(arr, l, ((l + r) / 2), r, monoid); 
        // build trees recursively using merge
        assert 2 * ((r + l) / 2 - l + 1) > powerTwo(treeHeight(buildTree(arr, l, (l + r) / 2, monoid)));
        assert 2 * (r - (r + l) / 2) > powerTwo(treeHeight(buildTree(arr, (l + r) / 2 + 1, r, monoid)));
        mergeTrees(
            buildTree(arr, l, (l + r) / 2, monoid), 
            buildTree(arr, (l + r) / 2 + 1, r, monoid), monoid.op)
        )
}
    
// lemma: for a tree with correct structure and correct values in children 
// value in root is combined value in children
lemma validTreeValuesRange<T(!new)>(tree: SegmentTree<T>, arr: array<T>, monoid: Monoid.AbstractMonoid<T>)
    // correct boundaries for the tree
    requires 0 <= boundaries(tree).0 <= boundaries(tree).1 < arr.Length
    // monoid needs to be correct
    requires monoid.validMonoid()
    // valid tree and values in the tree
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
        case Leaf(x, val) => assert validTreeValues(tree, arr, monoid);
        case Node(l, m, r, left, right, val) => 
            // if it is correct for left and right, and monoid is associative, we get the result
            validTreeValuesRange(left, arr, monoid);
            validTreeValuesRange(right, arr, monoid);
            associativeQuery(arr, l, m, r, monoid);
    }
}

// lemma: if we want to calulate fold for intersection of the segments, we can split one of them at point m,
// then just combine values of two results new subsegment - other segment
lemma splitSegmentQuery<T(!new)>(arr: array<T>, l: int, m: int, r: int, l1: int, r1: int, monoid: Monoid.AbstractMonoid<T>) 
    // need associativity
    requires monoid.validMonoid()
    // need valid boundaries
    requires 0 <= l <= m <= r < arr.Length
    requires 0 <= l1 <= r1 < arr.Length
    ensures straightQuery(arr, maxInt(l, l1), minInt(r, r1), monoid) == 
        monoid.op(straightQuery(arr, maxInt(l, l1), minInt(m, r1), monoid), straightQuery(arr, maxInt(m + 1, l1), minInt(r, r1), monoid))
{
    // one of subsegments has empty intersection
    if m < l1 {
        return;
    }
    if (m > r1) {
        return;
    }
    // otherwise result is just special case for associative lemma
    associativeQuery(arr, maxInt(l1, l), m, minInt(r1, r), monoid);
}

// lemma: for folds on subarray l,r on two arrays whose only difference is not inside [l, r], their results are the same (under one monoid) 
lemma almostEqualQueries<T(!new)>(arr1: array<T>, arr2: array<T>, l: int, r: int, pos: int, monoid: Monoid.AbstractMonoid<T>) 
    // arrays have same size and differ in at most one postion, which is outside [l, r] 
    requires arr1.Length == arr2.Length
    requires monoid.validMonoid()
    requires forall i :: 0 <= i < arr1.Length && i != pos ==> arr1[i] == arr2[i]
    // valid fold boundaries
    requires 0 <= l <= arr1.Length
    requires 0 <= r < arr1.Length
    requires pos < l || pos > r
    ensures straightQuery(arr1, l, r, monoid) == straightQuery(arr2, l, r, monoid)
    decreases r - l
{
    if (r < l) {
        return;
    }
    // recursive proof
    almostEqualQueries(arr1, arr2, l + 1, r, pos, monoid);
}

// lemma: if tree is valid by structure and values on some segment for array arr1, 
// and array arr2 differs in at most in one position from arr1 which is ouside of the tree,
// then tree is a valid tree for arr2
lemma almostEqualTrees<T(!new)>(tree: SegmentTree<T>, arr1: array<T>, arr2: array<T>, pos: int, monoid: Monoid.AbstractMonoid<T>) 
    // valid tree for arr by structure and values
    requires validTree(tree)
    requires 0 <= boundaries(tree).0 <= boundaries(tree).1 < arr1.Length
    requires monoid.validMonoid()
    requires validTreeValues(tree, arr1, monoid)
    // arr1 and arr2 differs in at most one position
    requires arr1.Length == arr2.Length
    requires forall i :: 0 <= i < arr1.Length && pos != i ==> arr1[i] == arr2[i]
    // which is outside of the tree
    requires pos > boundaries(tree).1 || pos < boundaries(tree).0
    ensures validTreeValues(tree, arr2, monoid)
{
    match tree {
        case Leaf(x, val) => assert arr1[x] == arr2[x];
        case Node(l, m, r, left, right, val) => 
            // use induction and almost equal query lemma
            almostEqualTrees(left, arr1, arr2, pos, monoid);
            almostEqualTrees(right, arr1, arr2, pos, monoid);
            almostEqualQueries(arr1, arr2, l, r, pos, monoid);
            assert validTreeValues(tree, arr2, monoid);
    }
}

function method powerTwo(x: int): (res: int)
    requires x >= 0
    ensures res >= 1
{
    if x == 0 
    then
        1
    else 2 * powerTwo(x - 1) 
}

predicate equalStructures<T>(tree1: SegmentTree<T>, tree2: SegmentTree<T>) 
    requires validTree(tree1)
    requires validTree(tree2)
{
    match tree1 {
        case Leaf(x, _) =>
            match tree2 {
                case Leaf(y, _) => x == y
                case Node(_, _, _, _, _, _) => false
            }
        case Node(l, m, r, left, right, _) =>
            match tree2 {
                case Leaf(_, _) => false
                case Node(l1, m1, r1, left1, right1, _) => l1 == l && m1 == m && r1 == r && equalStructures(left, left1) && equalStructures(right, right1)
            }
    }
}

lemma equalTreeStructures<T>(tree: SegmentTree<T>) 
    requires validTree(tree)
    ensures equalStructures(tree, tree)
{
}

lemma equalStructuresProperties<T>(tree1: SegmentTree<T>, tree2: SegmentTree<T>) 
    requires validTree(tree1)
    requires validTree(tree2)
    requires equalStructures(tree1, tree2)
    ensures treeHeight(tree1) == treeHeight(tree2)
    ensures balancedTree(tree1) <==> balancedTree(tree2)
{
}
// function that by valid (structure and value) tree for arr1 returns a valid tree for arr2, 
// knowing that arr1 and arr2 differ in at most one position
function method rebuildTree<T(!new)>(tree: SegmentTree<T>, arr1: array<T>, arr2: array<T>, pos: int, monoid: Monoid.AbstractMonoid<T>): (res: (SegmentTree<T>, int))
    reads arr2
    reads arr1
    // differ in at most one position
    requires arr1.Length == arr2.Length
    requires forall i :: 0 <= i < arr1.Length && i != pos ==> arr1[i] == arr2[i]
    // valid tree by structure and values
    requires validTree(tree)
    requires monoid.validMonoid()
    requires 0 <= boundaries(tree).0 <= boundaries(tree).1 < arr1.Length
    requires validTreeValues(tree, arr1, monoid)
    requires balancedTree(tree)
    // valid tree by structure and values on arr2
    ensures boundaries(res.0) == boundaries(tree)
    ensures validTree(res.0)
    ensures validTreeValues(res.0, arr2, monoid)
    ensures equalStructures(tree, res.0)
    ensures balancedTree(res.0)
    ensures 2 * treeHeight(res.0) + 1 >= res.1
    ensures res.1 >= 0
{
    if (pos < boundaries(tree).0 || pos > boundaries(tree).1) 
    then
        // if position is outside of the tree, by lemma tree itself works
        almostEqualTrees(tree, arr1, arr2, pos, monoid);
        equalTreeStructures(tree);
        equalStructuresProperties(tree, tree);
        (tree, 1)
    else
        match tree {
            // corner case: return another leaf with fixed value
            case Leaf(x, val) => assert pos == x; (Leaf(x, arr2[x]), 1)
            case Node(l, m, r, left, right, val) => 
                // one of the segments [l, m], [m + 1, r] won't contain position, and the other will be fixed by recursion
                if (m < pos) 
                then
                    almostEqualTrees(left, arr1, arr2, pos, monoid);
                    associativeQuery(arr2, l, m, r, monoid);
                    var prevResult := rebuildTree(right, arr1, arr2, pos, monoid);
                    assert equalStructures(right, prevResult.0);
                    equalTreeStructures(left);
                    assert equalStructures(left, left);
                    equalStructuresProperties(tree, mergeTrees(left, prevResult.0, monoid.op));
                    (mergeTrees(left, prevResult.0, monoid.op), prevResult.1 + 1)
                else
                    almostEqualTrees(right, arr1, arr2, pos, monoid);
                    associativeQuery(arr2, l, m, r, monoid);
                    var prevResult := rebuildTree(left, arr1, arr2, pos, monoid);
                    assert equalStructures(left, prevResult.0);
                    equalTreeStructures(right);
                    assert equalStructures(right, right);
                    equalStructuresProperties(tree, mergeTrees(prevResult.0, right, monoid.op));
                    (mergeTrees(prevResult.0, right, monoid.op), prevResult.1 + 1)
        }
}

// by array, position and value returns an array with value at position and equal other elements
method singleChange<T>(arr: array<T>, pos: int, elem: T) returns (res: array<T>)
    requires 0 <= pos < arr.Length 
    ensures arr.Length == res.Length
    ensures res[pos] == elem
    ensures forall i :: 0 <= i < arr.Length && (i != pos) ==> arr[i] == res[i]
{
    // create array of values
    var newArr := new T[arr.Length](_ => elem);
    var i := 0;
    // "fix" the array by copying elements from original array, skipping the input position
    while i < arr.Length
        // natural loop invariants
        invariant 0 <= i <= arr.Length
        invariant elem == newArr[pos]
        invariant forall j :: 0 <= j < i && (j != pos) ==> arr[j] == newArr[j]
    {
        // skip input position or copy element from original array
        if (i != pos) {
            newArr[i] := arr[i];
        }
        i := i + 1;
    }
    return newArr;
}

// predicate to check that tree is close to balanced, i.e. it's height is bounded by logn
predicate balancedTree<T>(tree: SegmentTree<T>) 
    requires validTree(tree)
{
    powerTwo(treeHeight(tree)) < 2 * (boundaries(tree).1 - boundaries(tree).0 + 1) && 
    match tree {
        case Leaf(_, _) => true
        case Node(_, _, _, left, right, _) => balancedTree(left) && balancedTree(right)
    }
}

lemma nondecreasingPowerTwo(x: int, y: int) 
    requires x >= y >= 0
    ensures powerTwo(x) >= powerTwo(y)
{
}

class SegmentTreeWrapper<T(!new)>
{
    var elems: array<T>
    var tree: SegmentTree<T>
    var monoid: Monoid.AbstractMonoid<T>

    // predicate for valid subtree inside wrapper.
    // we need: structure, values, valid boundaries, valid monoid
    predicate validSubtree(subTree: SegmentTree<T>)
        reads this
        reads elems
    {
        monoid.validMonoid() && validTree(subTree) && boundaries(subTree).0 >= 0 && boundaries(subTree).1 < elems.Length && validTreeValues(subTree, elems, monoid)
    }

    // whether tree field covers entire array
    predicate fullTree() 
        reads this
    {
        boundaries(tree) == (0, elems.Length - 1)
    }

    constructor(arr: array<T>, m: Monoid.AbstractMonoid<T>) 
        requires m.validMonoid()
        requires arr.Length > 0
        ensures monoid.validMonoid()
        ensures elems.Length == arr.Length == elems.Length
        ensures validSubtree(tree)
        ensures fullTree()
        ensures balancedTree(tree)
    {
        elems := arr;
        monoid := m;
        // construct valid by structure and values tree from an input array
        tree := buildTree(arr, 0, arr.Length - 1, m);
    }

    // by tree valid tree on elems field returns fold of intersection of input segment with tree
    function method innerQuery(subTree:SegmentTree<T>, l: int, r: int): (res: T)
        reads elems
        reads this
        // valid subsegment and valid tree by structure and values
        requires validSubtree(subTree)
        requires 0 <= l <= r < elems.Length
        requires 0 <= boundaries(subTree).0 < elems.Length
        requires 0 <= boundaries(subTree).1 < elems.Length
        // intersection of two segments
        ensures res == straightQuery(elems, maxInt(boundaries(subTree).0, l), minInt(boundaries(subTree).1, r), monoid)
        decreases subTree
    {
        var (leftPoint, rightPoint) := boundaries(subTree);
        if (r < leftPoint || l > rightPoint) 
        then
            // no intersection - no fold 
            assert monoid.identity() == straightQuery(elems, maxInt(leftPoint, l), minInt(rightPoint, r), monoid); 
            monoid.identity()
        else if (l <= leftPoint <= rightPoint <= r) 
            then
                //full intersection - value in root 
                assert straightQuery(elems, maxInt(l, leftPoint), minInt(r, rightPoint), monoid) == 
                    straightQuery(elems, leftPoint, rightPoint, monoid);
                getValue(subTree)
            else match subTree {
                case Node(leftPoint, m, rightPoint, left, right, value) =>
                // otherwise answer is combination of answers of children
                    splitSegmentQuery(elems, leftPoint, m, rightPoint, l, r, monoid);
                    assert straightQuery(elems, maxInt(l, leftPoint), minInt(r, rightPoint), monoid) == 
                        monoid.op(
                            straightQuery(elems, maxInt(leftPoint, l), minInt(m, r), monoid), 
                            straightQuery(elems, maxInt(m + 1, l), minInt(rightPoint, r), monoid)
                        );
                    monoid.op(innerQuery(left, l, r), innerQuery(right, l, r))
                // just leaf value in corner case
                case Leaf(_, val) => assert leftPoint == rightPoint; val
            }
    }

    // public method for user usage
    method query(l: int, r: int) returns (res: T)
        // valid boundaries
        requires 0 <= l < elems.Length
        requires 0 <= r < elems.Length
        // valid by structure and values tree covering entire segment
        requires validSubtree(tree)
        requires fullTree()
        // answer is expected
        ensures res == straightQuery(elems, l, r, monoid)
    {
        if (l > r) {
            return monoid.identity();
        }
        return innerQuery(tree, l, r);
    }

    // public method for an element update
    method change(pos: int, elem: T)
        modifies this
        // valid by structure and values tree covering entrire array
        requires monoid.validMonoid()
        requires validTree(tree)
        requires validSubtree(tree)
        requires fullTree()
        requires balancedTree(tree)
        // valid position
        requires 0 <= pos < elems.Length
        // key invariants kept
        ensures monoid.validMonoid()
        ensures validTree(tree)
        ensures validSubtree(tree)
        ensures fullTree()
        ensures balancedTree(tree)
        // elems almost equal to old elems, all but one are the same and input position contains new value
        ensures elems.Length == old(elems.Length) 
        ensures elems[pos] == elem
        ensures forall i :: 0 < i < elems.Length && (i != pos) ==> elems[i] == old(elems[i])
    {
        // update elems without modifying elems by index
        var newElems := singleChange(elems, pos, elem);
        // update tree by fixing malformed subtrees
        var newTree := rebuildTree(tree, elems, newElems, pos, monoid);
        elems := newElems;
        tree := newTree.0;
        var recursionCalls := newTree.1;
        assert recursionCalls <= 2 * treeHeight(tree) + 1;
        assert powerTwo(treeHeight(tree)) < 2 * elems.Length;
        nondecreasingPowerTwo(treeHeight(tree), (recursionCalls - 1) / 2);
        assert powerTwo((recursionCalls - 1) / 2) < 2 * elems.Length;       
    }
}

method Main() {
    // monoid examples
    var addMonoidInstance := new Monoid.AddMonoid();
    var minMonoidInstance := new Monoid.MinMonoid();
    print addMonoidInstance.op(3, 13), " ";
    print addMonoidInstance.identity(), " ";
    print minMonoidInstance.op(3, 13), " ";
    print minMonoidInstance.identity(), " ";
    assert addMonoidInstance.validMonoid();
    print "Our testing array for segment tree: 3, 1, 4, 1, 5, 9, 2\n";
    var arr := new int[7];
    arr[0] := 3;
    arr[1] := 1;
    arr[2] := 4;
    arr[3] := 1;
    arr[4] := 5;
    arr[5] := 9;
    arr[6] := 2;
    var minArr := new Monoid.BoundedInt[7];
    minArr[0] := 3;
    minArr[1] := 1;
    minArr[2] := 4;
    minArr[3] := 1;
    minArr[4] := 5;
    minArr[5] := 9;
    minArr[6] := 2;
    var segmentTreeAdd := new SegmentTreeWrapper<int>(arr, addMonoidInstance);  
    assert segmentTreeAdd.elems.Length == 7;
    var addRes24 := segmentTreeAdd.query(2, 4);
    print "add result on 2-4: ", addRes24, "\n";
    segmentTreeAdd.change(3, 8);
    var newAddRes24 := segmentTreeAdd.query(2, 4);
    print "add result on 2-4 after change: ", newAddRes24, "\n";
    assert arr[3] == 1;
    var segmentTreeMin := new SegmentTreeWrapper<Monoid.BoundedInt>(minArr, minMonoidInstance);
    assert segmentTreeMin.elems.Length == 7;
    var minRes35 := segmentTreeMin.query(3, 5);
    print "min result on 3-5: ", minRes35, "\n";
    segmentTreeMin.change(3, 8);
    var newMinRes35 := segmentTreeMin.query(3, 5);
    print "min result on 3-5 after change: ", newMinRes35, "\n";
    assert minArr[3] == 1;
}