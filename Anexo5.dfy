method mochila(P: array<real>, V: array<real>, M: real) returns (sol: array<real>, val: real)

	requires P.Length == V.Length && M > 0.0

{

	var x : array<real> := new real[P.Length] ;
	var valor : real ;

	valor := 0.0 ;

	var peso : real ;

	peso  := 0.0 ;
	
	var i : nat ;

	i := 0 ;

	while i < P.Length && peso < M {

		if peso + P[i] <= M {

			x[i], peso, valor := 1.0, peso + P[i], valor + V[i] ;

		} else {

			x[i], peso, valor := (M - peso) / P[i], M, valor + V[i] * (M - peso) / P[i] ;

		}

		i := i + 1 ;

	}


	while i < P.Length {

		x[i] := 0.0 ;

		i := i + 1 ;

	}

	return x, valor ;

}
