method QuickSort(arr: array<int>) returns (sortedArr: array<int>)
  ensures sortedArr.Length == arr.Length
  ensures forall i, j :: 0 <= i < j < sortedArr.Length ==> sortedArr[i] <= sortedArr[j]
{
  if arr.Length <= 1 {
    sortedArr := arr;
  } else {
    var pivot := arr[0];
    var lessThanPivot := [x | x in arr[1..] where x <= pivot];
    var greaterThanPivot := [x | x in arr[1..] where x > pivot];
    sortedArr := QuickSort(lessThanPivot) + [pivot] + QuickSort(greaterThanPivot);
  }
}
method Main()
{
  var arr := [5, 2, 9, 1, 3, 7, 8, 6, 4, 0];
  var sortedArr := QuickSort(arr);
  assert forall i, j :: 0 <= i < j < sortedArr.Length ==> sortedArr[i] <= sortedArr[j];
}