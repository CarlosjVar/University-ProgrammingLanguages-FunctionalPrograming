(* Determinar si una proposición es una tautología *)

(* exception NoEsUnaTautologia of (Identificador * bool) list *)

fun taut prop =
    let
    	(* variables de trabajo *)
    	val variables = vars prop
    	val n = length variables
    	val bools = gen_bools n
    	(* generar evaluaciones de la proposición*)
    	fun eval booleanos =
    		let
	    		fun recorrer []                  = Bien true
	    		|   recorrer (fila :: mas_filas) = 
	        		    let
	    		        	val asignacion = as_vals variables fila
	    		        	val evaluacion_es_verdadera = evalProp asignacion prop
	    		        in
	    		        	(* if evaluacion_es_verdadera then
	    		        		recorrer mas_filas
	    		        	else
	    		        	    raise NoEsUnaTautologia asignacion    *)
                            case evaluacion_es_verdadera of
                                (Bien true )  => recorrer mas_filas
                            |   (Bien false ) => NoEsUnaTautologia asignacion
                            |   otro          => otro
	    		        end
            in
                recorrer bools
            end
    in
    	(* if eval bools then imprimir prop ^ " SÍ es una tautología" else ""
    end handle NoEsUnaTautologia asignacion => imprimir prop ^ " NO es una tautología, porque " ^ impr_as_vals asignacion *)
        case eval bools of
            (Bien true)   => imprimir prop ^ " SÍ es una tautología"
        |   (Bien false ) => imprimir prop ^ " esto NO debería ocurrir..."
        |   (NoEsUnaTautologia asignacion) => imprimir prop ^ " NO es una tautología, porque " ^ impr_as_vals asignacion
        |   (NoEstaEnElDominio ident)      => "En " ^ imprimir prop ^ " la variable " ^ ident ^ "no aparece (esto NO debería ocurrir)"
    end
;
