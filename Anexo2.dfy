method QuickSort(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi < a.Length
{
    if lo < hi {
        var pivot := Partition(a, lo, hi);
        QuickSort(a, lo, pivot - 1);
        QuickSort(a, pivot + 1, hi);
    }
}

method Partition(a: array<int>, lo: int, hi: int) returns (pivotIndex: int)
    requires 0 <= lo <= hi < a.Length
{
    var pivotValue := a[hi];
    var i := lo;
    for j in lo .. hi {
        if a[j] < pivotValue {
            a[i], a[j] := a[j], a[i];
            i := i + 1;
        }
    }
    a[i], a[hi] := a[hi], a[i];
    pivotIndex := i;
}