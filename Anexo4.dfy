method FractionalKnapsack(weights: array<int>, values: array<int>, capacity: int) 
         returns (totalValue: real)
    requires weights.Length == values.Length && capacity >= 0
{
    var n := weights.Length;
    var ratios := new array<real>(n, 0.0);
    for i in 0 .. n {
        ratios[i] := real(values[i]) / real(weights[i]);
    }
    SortByRatio(weights, values, ratios);

    var currentWeight := 0;
    var currentValue := 0.0;
    var i := 0;
    while i < n && currentWeight < capacity {
        var remainingCapacity := capacity - currentWeight;
        var weightToAdd := min(remainingCapacity, weights[i]);
        currentWeight := currentWeight + weightToAdd;
        currentValue := currentValue + real(weightToAdd) * ratios[i];
        i := i + 1;
    }
    totalValue := currentValue;
}

method SortByRatio(weights: array<int>, values: array<int>, ratios: array<real>)
    requires weights.Length == values.Length
{
    var n := weights.Length;
    for i in 0 .. n {
        var maxIndex := i;
        for j in i + 1 .. n {
            if ratios[j] > ratios[maxIndex] {
                maxIndex := j;
            }
        }
        if maxIndex != i {
            weights[i], weights[maxIndex] := weights[maxIndex], weights[i];
            values[i], values[maxIndex] := values[maxIndex], values[i];
            ratios[i], ratios[maxIndex] := ratios[maxIndex], ratios[i];
        }
    }
}