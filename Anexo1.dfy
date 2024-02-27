method ordenar_quicksort(V : array?<int>)

    requires V != null
    requires V.Length >= 1
    
    modifies V
{ 
    quicksort(V, 0, V.Length) ;
}

predicate segmento_ordenado(V : array?<int>, c : int, f : int)

    requires V != null
    requires 0 <= c <= f <= V.Length
    
    reads V 
{
    forall j, k :: c <= j < k < f ==> V[j] <= V[k]
}



method quicksort(V : array?<int>, c : int, f : int)

    requires V != null && V.Length >= 1
    requires 0 <= c <= f <= V.Length
    requires 0 <= c <= f <  V.Length ==> 
                                     forall j :: c <= j < f ==> V[j] < V[f]
    requires 0 <  c <= f <= V.Length ==> 
                                     forall j :: c <= j < f ==> V[c - 1] <= V[j]

    ensures segmento_ordenado(V, c, f)
    ensures forall j :: 0 <= j < c || f <= j < V.Length ==> old(V[j]) == V[j]
    ensures 0 <= c <= f <  V.Length ==> 
                                     forall j :: c <= j < f ==> V[j] < V[f]
    ensures 0 <  c <= f <= V.Length ==> 
                                     forall j :: c <= j < f ==> V[c - 1] <= V[j]
                              
    decreases f - c

    modifies  V

{
    
    if f - c > 1 {

        var pivote : int ; 
	pivote := particion(V, c, f) ;
        
        quicksort(V, c, pivote) ;
        quicksort(V, pivote + 1, f) ;
        
    } else {
        
        return ;  
    }
}

method particion(V : array?<int>, c : int, f : int) returns (pivote : int)

    requires V != null && V.Length > 0
    requires 0 <= c <  f <= V.Length
    requires 0 <= c <= f <  V.Length ==> 
                                     forall j :: c <= j < f ==> V[j] < V[f]
    requires 0 <  c <= f <= V.Length ==> 
                                     forall j :: c <= j < f ==> V[c - 1] <= V[j]
                                          
    ensures  0 <= c <= pivote < f <= V.Length
    ensures  forall j :: c      <= j < pivote ==> V[j] < V[pivote]
    ensures  forall j :: pivote <  j < f      ==> V[pivote] <= V[j]
    ensures  forall j :: 0      <= j < c || f <= j < V.Length ==> old(V[j]) == V[j]
    ensures  0 <= c <= f <  V.Length ==> 
                                    forall j :: c <= j < f ==> V[j] < V[f]
    ensures  0 <  c <= f <= V.Length ==> 
                                    forall j :: c <= j < f ==> V[c - 1] <= V[j]
                    
    modifies V
                            
{
    
    pivote := c ;

    var indice : nat ;
    indice := c + 1 ;
    
    while indice < f
    
        invariant c <= pivote < indice <= f
        invariant forall j :: c      <= j < pivote ==> V[j] < V[pivote]
        invariant forall j :: pivote <  j < indice ==> V[pivote] <= V[j]
        invariant forall j :: 0      <= j < c || f <= j < V.Length ==> old(V[j]) == V[j]
        invariant 0 <= c <= f <  V.Length ==> 
                                          forall j :: c <= j < f ==> V[j] < V[f]
        invariant 0 <  c <= f <= V.Length ==> 
                                          forall j :: c <= j < f ==> V[c - 1] <= V[j]
                     
    {
        
        if V[indice] < V[pivote]
        
        {
            
            assert 0 < c <= f <= V.Length ==> 
                                          forall j :: c <= j < f ==> V[c - 1] <= V[j] ;
                     
            var contador : nat ;
            contador := indice - 1 ;

            var temp : int ;
            temp := V[indice] ;
            
            V[indice] := V[contador] ;
            
            while contador > pivote
            
                invariant forall j :: c      <= j < pivote     ==> V[j] < V[pivote]
                invariant forall j :: pivote <  j < indice + 1 ==> V[pivote] <= V[j]
                invariant V[pivote] > temp
                invariant forall j :: 0 <= j < c || f <= j < V.Length ==> old(V[j]) == V[j]
                invariant 0 <= c <= f <  V.Length ==>
                                                  forall j :: c <= j < f ==> V[j] < V[f]
                invariant 0 <  c <= f <= V.Length ==> 
                                                  forall j :: c <= j < f ==> V[c - 1] <= V[j]
                              
            {
                V[contador + 1] := V[contador] ;
                contador := contador - 1 ;  
            }
            
            V[pivote + 1] := V[pivote] ;
            pivote        := pivote + 1 ;
            V[pivote - 1] := temp ;
            
        }
        
        indice := indice + 1 ;
    }  
}