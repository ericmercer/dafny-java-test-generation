predicate isSorted(arr: array<int>) 
  reads arr
{
  forall i: int :: 0 < i < arr.Length ==> arr[i] >= arr[i-1]
}

// This method satifies the contract, but is obviously wrong.
// This shows the issue of having a weak contract, which the test exposes.
method sort(arr: array<int>)
  modifies arr
  ensures arr.Length == old(arr.Length)
  ensures isSorted(arr)
{
  var i: int := 0;
  while (i < arr.Length)
    decreases arr.Length - i
    invariant 0 <= i <= arr.Length
    invariant forall j: int :: 0 <= j < i ==> (arr[j] == j)
  {
    arr[i] := i;
    i := i + 1;
  }
}

// Using the same test case from the Java Unit Test exposes the weakness
//   of the specification
method sortArrayTest()
{
  var myArray := new int[3];
  myArray[0] := 5;
  myArray[1] := 13;
  myArray[2] := 1;
  var oldLength := myArray.Length;
  sort(myArray);  // Specification is not strong enough to prove the following asserts
  assert(isSorted(myArray));
  assert(oldLength == myArray.Length);
}