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

/*predicate validTree<T(!new)>(tree: array<T>, monoid: Monoid.AbstractMonoid<T>) 
reads tree
requires monoid.validMonoid()
{
    forall i :: 0 < i < tree.Length / 2 ==> tree[i] == monoid.op(tree[2 * i], tree[2 * i + 1])
}

method updateTree<T(!new)>(
    index: int, 
    n: int, 
    elems: array<T>, 
    monoid: Monoid.AbstractMonoid<T>, 
    elem: T
    ) returns  (res: array<T>)
    requires elems.Length == 2 * n
    requires forall i :: 0 <= i < n ==> elems[i] == monoid.op(elems[2 * i], elems[2 * i + 1]) 
    requires monoid.validMonoid()
    requires 0 <= index < n 
    requires validTree(elems, monoid)
    ensures validTree(res, monoid)
    ensures res.Length == 2 * n
{
    var newTree := new T[2 * n](i => elem);
    var i := 0;
    while i < 2 * n 
    invariant 0 <= i <= 2 * n
    invariant forall j :: 0 <= j < i && j != index + n ==> newTree[j] == elems[j] 
    {
        if i != index + n {
            newTree[i] := elems[i];
        }
        i := i + 1;
    }
    var pnt := index + n;
    pnt := pnt / 2;
    while pnt > 0
    invariant 0 <= pnt < n
    invariant forall vert :: (0 < vert < pnt) && (vert / 2 != pnt) ==> newTree[vert] == monoid.op(newTree[2 * vert], newTree[2 * vert + 1])
    {
        pnt := pnt / 2;
    }
    return newTree;
}*/

predicate isPowerTwo(s: bv32)
{
    s > 0 && (s & (s - 1) == 0)
}

predicate allSplit(splitSeq: seq<(int, int)>, start: int, end: int)
{
    |splitSeq| == 0 || (splitSeq[0].0 == start && splitSeq[|splitSeq| - 1].1 == end &&
    forall i :: 0 < i < |splitSeq| ==> splitSeq[i - 1].1 + 1 == splitSeq[i].0)
}

predicate powTwoSeq(splitSeq: seq<(int, int)>, twoPower: int) 
    requires twoPower >= 1
    //requires isPowerTwo(twoPower)
{
    |splitSeq| == 0 || (forall i :: 0 <= i < |splitSeq| ==> splitSeq[i] == (twoPower * i, twoPower * (i + 1) - 1))
}


lemma powTwoDiv(x: bv32, y: bv32) 
    requires x >= y >= 1
    requires isPowerTwo(x)
    requires isPowerTwo(y)
    ensures isPowerTwo(x / y)
{
    assert isPowerTwo(x / y);
}

/*method createBoundaries(n: int) returns (res: array<(int, int)>)
    requires n > 1 
    requires isPowerTwo(n)
    ensures res.Length == n
    //ensures forall twoPower: nat :: isPowerTwo(twoPower) && 1 <= twoPower <= n / 2 ==> allSplit(res[twoPower..2 * twoPower], 0, n / 2 - 1)
    //ensures forall i :: 1 <= i < n / 2 ==> res[i] == (res[2 * i].0, res[2 * i + 1].1)
    decreases n
{
    if (n == 2) {
        var arr := new (int, int)[2];
        arr[1] := (0, n / 2 - 1);
        //assert forall twoPower: nat :: isPowerTwo(twoPower) && 1 <= twoPower <= n / 2 ==> allSplit(arr[twoPower .. 2 * twoPower], 0, n / 2 - 1);
        return arr;
    } 
    var arr := new (int, int)[n];
    var twoPower := n / 2;
    var compTwoPower := 1;
    var index := twoPower;
    while index < twoPower * 2
        invariant twoPower <= index <= 2 * twoPower
        invariant forall grtTwoPower: nat :: isPowerTwo(grtTwoPower) && 2 * twoPower <= grtTwoPower <= n / 2 ==> 
            powTwoSeq(arr[grtTwoPower..2 * grtTwoPower], n / 2 / grtTwoPower)
        //invariant forall j :: twoPower <= j <= index ==> allSplit(arr[twoPower..j], 0, (j - twoPower) * compTwoPower - 1)
        //invariant forall grtTwoPower: nat :: isPowerTwo(grtTwoPower) && 2 * twoPower <= grtTwoPower <= n / 2 ==> 
        //    allSplit(arr[grtTwoPower..2 * grtTwoPower], 0, n / 2 - 1)    
    {
        arr[index] := ((index - twoPower) * compTwoPower, (index - twoPower) * compTwoPower + compTwoPower - 1);
        index := index + 1;
    }
    twoPower := twoPower / 2;
    compTwoPower := compTwoPower * 2;
    
    while twoPower > 1
        invariant 1 <= twoPower <= n
        invariant isPowerTwo(twoPower)
        invariant isPowerTwo(compTwoPower)
        invariant compTwoPower * twoPower == n / 2 
        invariant forall grtTwoPower: nat :: isPowerTwo(grtTwoPower) && 2 * twoPower <= grtTwoPower <= n / 2 ==> 
            powTwoSeq(arr[grtTwoPower..2 * grtTwoPower], n / 2 / grtTwoPower)
        //invariant forall grtTwoPower: nat :: isPowerTwo(grtTwoPower) && 2 * twoPower <= grtTwoPower <= n / 2 ==> 
        //    allSplit(arr[grtTwoPower..2 * grtTwoPower], 0, n / 2 - 1)
    {
        var i := twoPower;
        while i < twoPower * 2
            invariant twoPower <= i <= 2 * twoPower
            invariant forall j :: twoPower <= j < i ==> arr[j] == ((j - twoPower) * compTwoPower, (j - twoPower) * compTwoPower + compTwoPower - 1)
            invariant forall j :: twoPower <= j <= i ==> allSplit(arr[twoPower..j], 0, (j - twoPower) * compTwoPower - 1)
            //invariant forall grtTwoPower: nat :: isPowerTwo(grtTwoPower) && 2 * twoPower <= grtTwoPower <= n / 2 ==> 
            //    allSplit(arr[grtTwoPower..2 * grtTwoPower], 0, n / 2 - 1)    
        {
            //assert allSplit(arr[twoPower..i], 0, (i - twoPower) * compTwoPower - 1);
            arr[i] := ((i - twoPower) * compTwoPower, (i - twoPower) * compTwoPower + compTwoPower - 1);
            i := i + 1;
        }
        //assert allSplit(arr[twoPower..twoPower * 2], 0, n / 2 - 1);
        //powerTwoIneq(twoPower); 
        //assert forall grtTwoPower: nat :: isPowerTwo(grtTwoPower) && 2 * twoPower <= grtTwoPower <= n / 2 ==> 
        //    allSplit(arr[grtTwoPower..2 * grtTwoPower], 0, n / 2 - 1);
        twoPower := twoPower / 2;
        compTwoPower := compTwoPower * 2;
        //assert forall grtTwoPower: nat :: isPowerTwo(grtTwoPower) && 2 * twoPower <= grtTwoPower <= n / 2 ==> 
        //    grtTwoPower == 2 * twoPower || grtTwoPower >= twoPower * 4;
        //assert forall grtTwoPower: nat :: isPowerTwo(grtTwoPower) && 4 * twoPower <= grtTwoPower <= n / 2 ==> 
        //    allSplit(arr[grtTwoPower..2 * grtTwoPower], 0, n / 2 - 1);
    }
    //assert forall grtTwoPower: nat :: isPowerTwo(grtTwoPower) && 2 <= grtTwoPower <= n / 2 ==> 
    //        allSplit(arr[grtTwoPower..2 * grtTwoPower], 0, n / 2 - 1);
    arr[1] := (0, n / 2 - 1);
    return arr;
}
*/

class SegmentTree<T(!new, ==)> {
    var monoid: Monoid.AbstractMonoid<T>
    var elems: array<T>
    var boundaries: array<(int, int)>
    var n: nat
    predicate validSize() 
        reads this
        requires n <= 10_000
    {
        2 * n == elems.Length && isPowerTwo(n as bv32)
    }
    constructor(m: Monoid.AbstractMonoid<T>, size: int) 
        requires size >= 1
        requires size <= 1_000
        requires m.validMonoid()
        ensures n >= size
        ensures size * 2 >= n
        ensures validSize()
        ensures valid()
        ensures monoid.validMonoid()
    {
        monoid := m;
        var hf: bv32 := 1 as bv32;
        while (hf as int < size)
            invariant 1 <= hf as int <= size * 2
            invariant isPowerTwo(hf)
        {
            hf := hf >> 1;
        }
        n := hf as int;
        assert hf as int <= 2 * size;
        elems := new T[2 * hf as int](i => m.identity());
    }
    predicate valid() 
        reads this
        reads elems
        requires n < 10_000
        requires validSize()
    {
        forall i: int :: 0 < i < n ==> elems[i] == monoid.op(elems[2 * i], elems[2 * i + 1])
    }

    /*method setBoundaries()
        modifies this
        requires isPowerTwo(n) && n >= 1
        ensures boundaries.Length == 2 * n
        ensures forall lvl: nat :: isPowerTwo(lvl) && 1 <= lvl <= n ==> allSplit(boundaries[lvl..lvl * 2], 0, n - 1)
    {   
        boundaries := createBoundaries(2 * n);
    }*/
    
    /*method changeElement(index: int, elem: T)
        modifies elems
        requires 0 <= index < n
        requires validSize()
        requires valid()
        ensures valid()
        ensures elems[index + n] == elem
    {
        var pnt := index + n;
        elems[pnt] := elem;
        while pnt > 1
            invariant forall i: int :: 0 < i < n && 2 * i != pnt && 2 * i + 1 != pnt ==> elems[i] == monoid.op(elems[2 * i], elems[2 * i + 1])
            invariant elems[index + n] == elem
            invariant pnt / 2 < n
        {
            pnt := pnt / 2;
            elems[pnt] := monoid.op(elems[pnt * 2], elems[pnt * 2 + 1]);
        }
    }*/

    function straightQuery(l: int, r: int): (res: T) 
        reads this
        reads elems
        requires 0 <= l <= n && 0 <= r < n
        requires validSize()
        requires monoid.hasIdentity()
        ensures r == l ==> res == elems[l + n]
        ensures r < l ==> res == monoid.identity()
        decreases n - l
    {
        if l > r then monoid.identity() else monoid.op(elems[l + n], straightQuery(l + 1, r))
    }

    lemma associativeQuery(l: int, r: int, m: int) 
        requires 0 <= l <= m <= r < n
        requires validSize()
        requires monoid.validMonoid()
        ensures straightQuery(l, r) == monoid.op(straightQuery(l, m), straightQuery(m + 1, r))
        decreases r - l
    {
        if (r == m) {
            assert straightQuery(l, r) == monoid.op(straightQuery(l, m), straightQuery(m + 1, r));
            return;
        }
        assert straightQuery(l, r) == monoid.op(straightQuery(l, m), straightQuery(m + 1, r));
    }
}

method Main() {
    var addMonoidInstance := new Monoid.AddMonoid();
    var minMonoidInstance := new Monoid.MinMonoid();
    var minMonoidSt := new Monoid.MinMonoid();
    assert minMonoidSt.validMonoid();
    var segmentTreeInstance := new SegmentTree<Monoid.BoundedInt>(minMonoidSt, 6);
    print segmentTreeInstance.elems[0], "\n";
    assert segmentTreeInstance.validSize();
    //segmentTreeInstance.changeElement(0, 8);
    //print segmentTreeInstance.straightQuery(0, 1);
    print addMonoidInstance.op(3, 13), " ";
    print addMonoidInstance.identity(), " ";
    print minMonoidInstance.op(3, 13), " ";
    print minMonoidInstance.identity(), " ";
    assert addMonoidInstance.validMonoid();    
}