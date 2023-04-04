predicate sorted(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  reads a
{
  forall j, k :: lo <= j < k < hi ==> a[j] <= a[k]
}

function heapsize(a: array<int>): int
  reads a
  requires a.Length > 0
{ a[0] }

predicate isMaxHeap(a: array<int>)
  // requires a.Length > 0
  reads a
{
  0 < a.Length &&
  1 <= heapsize(a) < a.Length &&
  forall i | 1 < i <= heapsize(a) :: a[parent(i)] >= a[i]
}

// parent node id in the tree
function parent(i: int) : int
{  i / 2 }

// left child id in the tree
function lchild(i: nat) : int
  ensures parent(lchild(i)) == i
{ 2 * i }

// TODO add rchild
function rchild(i: nat) : int
  ensures parent(rchild(i)) == i
{2 * i + 1}

predicate maxIndex(a: array<int>, n: nat, m: int)
  reads a
{ 0 < a.Length &&
  1 <= m <= n <= heapsize(a) < a.Length &&
  forall k | 1 <= k <= n :: a[k] <= a[m]
}

lemma {:verify true} LemmaHeapMax(a: array<int>, n: nat)
  requires a.Length > 0
  requires 1 <= n <= heapsize(a)
  requires isMaxHeap(a)
  ensures maxIndex(a, n, 1)
{

  if n == 1 {
    assert forall k | 1 <= k <= 1 :: a[k] <= a[1];
  } else {
    assert n != 1 ==> a[parent(n)] >= a[n];
    LemmaHeapMax(a, n - 1);
  }

  assert maxIndex(a, n, 1);
}

// turn array a into a heap; bubble up out of place elements
method {:verify true} Heapify(a: array<int>)
  modifies a;
  requires a.Length > 1;
  ensures multiset(a[1..]) == multiset(old(a[1..]));
  ensures heapsize(a) == a.Length - 1
  ensures isMaxHeap(a);
{

  a[0] := 1;

  while heapsize(a) < a.Length - 1
    invariant  1 <= heapsize(a) < a.Length;
    invariant isMaxHeap(a)
    invariant multiset(a[1..]) == multiset(old(a[1..]))
    decreases a.Length - heapsize(a)
  {
    a[0] := a[0] + 1;

    ghost var n := heapsize(a);
    var lastNode := heapsize(a);
    var theParent := parent(lastNode);

    while lastNode > 1 && a[lastNode] > a[theParent]
      invariant 1 <= lastNode <= heapsize(a)
      invariant 0 <= theParent < heapsize(a)
      invariant 1 <= heapsize(a) < a.Length
      invariant forall i | 1 < i <= heapsize(a) && i != lastNode :: a[parent(i)] >= a[i]
      invariant forall i | 1 < i <= heapsize(a) && parent(i) == lastNode && lastNode > 1 :: a[parent(parent(i))] >= a[i]
      invariant n == a[0]
      invariant multiset(a[1..]) == multiset(old(a[1..]))
      invariant theParent == parent(lastNode)
      decreases lastNode
    {
      var temp := a[lastNode];
      a[lastNode] := a[theParent];
      a[theParent] := temp;

      lastNode := theParent;
      theParent := parent(lastNode);
    }
  }
}

// turn a into a sorted array by putting the head of a to the end
// and insert the last element of the heap at the top and bubble it down
method {:verify true} UnHeapify(a: array<int>)
  modifies a
  requires a.Length > 1
  requires heapsize(a) == a.Length - 1
  requires isMaxHeap(a)
  ensures multiset(a[1..]) == multiset(old(a[1..]))
  ensures sorted(a, 1, a.Length)
{
  assert isMaxHeap(a);
  LemmaHeapMax(a, heapsize(a));

  while 0 < a[0]
    invariant 0 <= a[0] <= a.Length - 1
    invariant a[0] == heapsize(a)
    invariant multiset(a[1..]) == multiset(old(a[1..]))
    invariant forall i | 1 < i <= heapsize(a) :: a[parent(i)] >= a[i]
    //everything element in the array at a position smaller or equal to heapsize(a) is in a maxheap, and everything at a position bigger than heapsize(a) is ordered
    //this invariant below ensures that at each iteration a[heapsize(a)] and a[1] to be smaller than a[i](the elements at the end of the array which should be in sorted order 
    //and are not in the heap anymore), this is to ensure the sorted property, that when we add the a[1] element
    //from the heap we can be sure that it is smaller than the already sorted elements on the right side of the element at position heapsize(a)
    invariant forall i | heapsize(a) < i < a.Length :: a[heapsize(a)] <= a[i] && a[1] <= a[i]
    invariant sorted(a, a[0] + 1, a.Length)
    decreases a[0]
  {
    LemmaHeapMax(a, a[0]);
 
    var trans := a[1];
    a[1] := a[a[0]];
    a[a[0]] := trans;

    a[0] := a[0] - 1;


    var i := 1;
    ghost var n := a[0];

    while ((lchild(i) <= a[0] && a[i] < a[lchild(i)] && lchild(i) != heapsize(a)) || (rchild(i) <= a[0] && a[i] < a[rchild(i)] && rchild(i) != heapsize(a)))
      invariant 0 <= a[0] <= a.Length - 1
      invariant sorted(a, a[0] + 1, a.Length)
      invariant n == a[0]
      invariant 1 <= i <= heapsize(a)
      invariant i > 1 ==> a[parent(i)] >= a[i]
      invariant multiset(a[1..]) == multiset(old(a[1..]))
      decreases a.Length - i
    {
      var trans2 := a[i];

      if (rchild(i) <= a[0] && a[lchild(i)] >= a[rchild(i)] && lchild(i) != heapsize(a)) || !(rchild(i) <= a[0]) {
        a[i] := a[lchild(i)];
        a[lchild(i)] := trans2;
        i := lchild(i);
      
      } else {
        a[i] := a[rchild(i)];
        a[rchild(i)] := trans2;
        i := rchild(i);
      }
    }

  }
}

method {:verify true} HeapSort(a: array<int>)
  modifies a
  requires a.Length > 0
  ensures multiset(a[1..]) == multiset(old(a[1..]))
  ensures sorted(a, 1, a.Length)
{
  if a.Length < 2 { return; }
  Heapify(a);
  UnHeapify(a);
}



