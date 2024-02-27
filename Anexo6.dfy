method MochilaFraccionaria(valores: array<int>, pesos: array<int>, capacidad: int) 
                           returns (valorTotal: int, mochila: array<(int, int, real)>)
    requires valores.Length == pesos.Length && capacidad >= 0;
    ensures  valorTotal >= 0 && valorTotal <= SumaValores(valores) && 
             mochila.Length <= valores.Length && 
             ParaTodo(i: int :: 0 <= i < mochila.Length ==> mochila[i].1 > 0 &&
             mochila[i].2 >= 0 && mochila[i].2 <= 1);

{

    var relaciones : array<(real, int, int)> := new (real, int, int)[valores.Length];
    var relacion : real;
    var valor : int;
    var peso : int;

    for i in 0 .. valores.Length - 1 {
        valor := valores[i];
        peso := pesos[i];
        relacion := valor / peso;
        relaciones[i] := (relacion, valor, peso);
    }

    QuickSort(relaciones, 0, relaciones.Length - 1);

    var valorTotalAcumulado := 0;
    var pesoTotalAcumulado := 0;
    var mochilaTmp := new array<(int, int, real)>(valores.Length);
    var indiceMochila := 0;

    for i in 0 .. relaciones.Length - 1 {
        var relacionActual := relaciones[i];
        var valorActual := relacionActual.1;
        var pesoActual := relacionActual.2;

        if pesoTotalAcumulado + pesoActual <= capacidad {
            mochilaTmp[indiceMochila] := (valorActual, pesoActual, 1.0);
            indiceMochila := indiceMochila + 1;
            valorTotalAcumulado := valorTotalAcumulado + valorActual;
            pesoTotalAcumulado := pesoTotalAcumulado + pesoActual;
        }
        else {
            var fraccion := real.FromInt(capacidad - pesoTotalAcumulado) / 
                                 real.FromInt(pesoActual);
            mochilaTmp[indiceMochila] := (valorActual, pesoActual, fraccion);
            valorTotalAcumulado := valorTotalAcumulado + valorActual * fraccion;
            break;
        }
    }

    mochila := new array<(int, int, real)>(indiceMochila);
    for j in 0 .. indiceMochila - 1 {
        mochila[j] := mochilaTmp[j];
    }

    valorTotal := valorTotalAcumulado;
    
}

method QuickSort(arr: array<(real, int, int)>, low: int, high: int)
    modifies arr;
    ensures OrdenadoPorRelacion(arr, low, high);
{
    var i := low;
    var j := high;
    var pivot := arr[(low + high) / 2];

    while i <= j {
        while arr[i].0 > pivot.0 {
            i := i + 1;
        }
        while arr[j].0 < pivot.0 {
            j := j - 1;
        }
        if i <= j {
            var temp := arr[i];
            arr[i] := arr[j];
            arr[j] := temp;
            i := i + 1;
            j := j - 1;
        }
    }

    if low < j {
        QuickSort(arr, low, j);
    }
    if i < high {
        QuickSort(arr, i, high);
    }
}

function SumaValores(arr: array<int>) : int
{
    var suma := 0;
    for i in arr {
        suma := suma + i;
    }
    return suma;
}

function OrdenadoPorRelacion(arr: array<(real, int, int)>, low: int, high: int) : bool
    decreases high - low + 1;
{
    var i := low;
    while i < high {
        if arr[i].0 < arr[i + 1].0 {
            return false;
        }
        i := i + 1;
    }
    return true;
}

method Main() {
    var valores := [60, 100, 120];
    var pesos := [10, 20, 30];
    var capacidad := 50;

    var valorTotal : int;
    var mochila : array<(int, int, real)>;
    (valorTotal, mochila) := MochilaFraccionaria(valores, pesos, capacidad);

    assert valorTotal == 240;
    assert mochila.Length == 2;
    assert mochila[0] == (60, 10, 1.0);
    assert mochila[1] == (100, 20, 1.0);
}