// ASSIGNMENT 1
// CMSC 433 SPRING 2026
// PERFECT SCORE:  100 POINTS
//
// This assignment contains nine questions, each of which involves writing Dafny
// code. You should include your solutions in a single Dafny file and submit it using
// Gradescope.


// Question 1 (5 points)
//
// Fill in a requires clause that enables Dafny to verify
// method PlusOne

method PlusOne (x : int) returns (y : int)
    requires x >= 0 // TODO
    ensures y > 0
{
    y := x+1;
}

// Question 2 (5 points)
//
// Fill in requires clause(s) that enable(s) Dafny to verify the array bounds
// in method Swap (which swaps elements i and j in array a).

method Swap (a : array<int>, i : int, j : int)
    requires 0<=i< a.Length && 0<=j<a.Length// TODO
    modifies a  // Dafny requires listing of objects modified in a method
{
    var tmp : int := a[i];
    a[i] := a[j];
    a[j] := tmp;
}

// Question 3 (5 points)
//
// Give ensures clause(s) asserting that d is the result, and r the
// remainder, of dividing m by n.  Your clauses cannot use "/" or "%" (which are
// the Dafny division and mod operators, respectively). By definition, the
// remainder must be non-negative.

method IntDiv (m : int, n : int) returns (d : int, r : int)
    requires n > 0
    ensures d*n + r == m
{
    return m / n, m % n;
}

// Question 4 (5 points)
//
// Give ensures clause(s) asserting that the return value has the same
// length as array a and contains as its elements the sum of the
// corresponding elements in arrays a and b.

method ArraySum (a : array<int>, b : array<int>) returns (c : array<int>)
    requires a.Length == b.Length
    ensures c.Length == a.Length // FIXME
    ensures fresh(c)
    ensures forall j : int :: 0 <= j < a.Length ==> c[j] == a[j] + b[j]
{
    c := new int [a.Length];  // Creates new array of size a.Length
    var i : int := 0;
    while (i < a.Length)
        invariant i <= a.Length
        invariant forall j : int :: 0 <= j < i ==> c[j] == a[j] + b[j]
    {
        c[i] := a[i] + b[i];
        i := i + 1;
    }
}

// Question 5 (10 points)
//
// Give invariant(s) that enable(s) Dafny to verify the following program, which
// returns true if and only if array a is sorted.

method IsSorted (a : array<int>) returns (isSorted : bool)
    ensures isSorted <==> forall j : int :: 1 <= j < a.Length ==> a[j-1] <= a[j]
{
    isSorted := true;
    var i : int := 1;
    if (a.Length < 2)
    {
        return;
    }
    else
    {
        while (i < a.Length)
            invariant i <= a.Length
            invariant isSorted <==> forall j : int :: 1 <= j < i ==> a[j-1] <= a[j]
        {
            if a[i-1] > a[i]
            {
                return false;
            }
            i := i+1;
        }
    }
}

// Question 6 (20 points)
//
// Implement, and have Dafny verify, the method IsPrime below, which returns true
// if and only if the given positive integer is prime.

method IsPrime (m : int) returns (isPrime : bool)
    requires m > 0
    ensures isPrime <==> (m > 1 && forall j : int :: 2 <= j < m ==> m % j != 0)
{
    var i : int := 2;
    if m <= 1 {
        return false; 
    }
    isPrime := true; 
    while i < m 
        invariant 2 <= i <= m
        invariant isPrime <==> (forall j : int :: 2 <= j < i ==> m % j != 0 )
        {
        if m % i == 0 {
            isPrime := false ; 
            break ; 
        }
        i := i+1; 
    }
}

// Question 7 (20 points)
//
// Implement, and have Dafny verify, the method Reverse below, which returns a new array
// aRev consisting of the elements of a, but in reverse order.  To create a new 
// array of ints use the Dafny command "new int[...]", where "..." is the number
// of elements in the array.

method Reverse (a : array<int>) returns (aRev : array<int>)
    ensures aRev.Length == a.Length
    ensures forall i : int :: 0 <= i < a.Length ==> a[i] == aRev[aRev.Length-i-1]
    ensures fresh(aRev) // Indicates returned object is newly created in method body
{
    aRev := new int[a.Length];
    var i : int := a.Length;
    while i > 0 
    invariant 0 <= i <= a.Length
    invariant forall j : int ::  i<= j < a.Length ==> a[j] == aRev[a.Length-1 -j]

    {
        i := i -1 ; 
        aRev[a.Length -1 -i ] := a[i] ; 
    }
}

// Question 8 (15 points)

/*
    Here is a program that computes the series:
    [1 + 2 + 2^2 + ... + 2^m = 2^(m+1) - 1]

    x := 0;
    y := 1;
    z := 1;
    while x != m {
      z := 2 * z;
      y := y + z;
      x := x + 1;
    }
    end

    Fill in the following decorated program - you can use the following
    function in your assertions and invariants. Do NOT remove the numbers or
    change anything else about the programs. Only replace "FILL_IN_HERE" with
    your assertions---they should be valid Dafny propositions.
*/

function pow2(n : nat) : nat {
  match n 
  case 0 => 1
  case _ => 2 * (pow2 (n-1))
}

/* 
    { true } ->
(1)    { 1 == pow2(0+1) -1 }
      x := 0;
(2)    { 1 == pow2(x+1) -1 }
      y := 1;
(3)    { y == pow2(x+1) -1 && 1 == pow2(x) };
      z := 1;
(4)    {  y == pow2(x+1) -1 && z == pow2(x)  }
      while x != n {
(5)       {   y == pow2(x+1) -1 && z == pow2(x)  && x != n } ->
(6)       { y + 2*z == pow2(x + 2) -1 && 2*z == pow2(x + 1)  }
        z := 2 * z;
(7)       { y + z == pow2(x + 2) -1 && z == pow2(x+1) }
        y := y + z;
(8)       { y == pow2(x + 2) -1 && z == pow2(x+1) }
        x := x + 1;
(9)       {  y == pow2(x + 1) -1 && z == pow2(x) }
      }
(10)  {  y == pow2(x+1) -1 && z == pow2(x) && x == n } ->
      { y == pow2 (n+1) - 1 }
*/


// Question 9 (15 points)
/*
    Here is a pretty inefficient way of adding 3 numbers:

     x := 0;
     y := 0;
     z := c;
     while x != a {
       x := x + 1;
       z := z + 1;
     };
     while y <> b {
       y := y + 1;
       z := z + 1;
     }

    Show that it does what it should by completing the
    following decorated program. Again, do NOT remove the letters or
    change anything else about the programs. Only replace "FILL_IN_HERE" with
    your assertions---they should be valid Dafny propositions.
*/

/*
    { true } ->
(a) { 0 + 0 + c == 0 + 0 + c }
      x := 0;
(b)                { x == 0 }
      y := 0;
(c)                { y == 0 && c == x + c  }
      z := c;
(d)                { y == 0 && z == x + 0 + c  }
      while x != a {
(e)                { y == 0 && z == x + c && x != a  } ->
(f)                { y == 0 && z + 1 == (x + 1) + c  }
        x := x + 1;
(g)                { y == 0 && z + 1 == x + c  }
        z := z + 1;
(h)                { y == 0 && z == x + c  }
      end;
(i)                { y == 0 && z == x + c && a == x } ->
(j)                { z == a + c + y }
      while y != b {
(k)                { z == a + c + y && y != b } ->
(l)                { z + 1 == a + c + (y + 1) }
        y := y + 1;
(m)                { z + 1 == a + c + y }
        z := z + 1;
(n)                { z == a + c + y }
      }
(o) { z == a + c + y && y == b  } ->
    { z == a + b + c }
*/