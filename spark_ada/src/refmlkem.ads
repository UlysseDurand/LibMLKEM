
with SPARK.Big_Integers; use SPARK.Big_Integers;
with SumGen; use SumGen;

package RefMLKEM
    with SPARK_Mode => On
is

    package ZqRef 
        with SPARK_Mode => On
    is

        Q : constant := 3329;

        type T_Ref is mod Q;

        Psi_Zero : constant T_Ref := 17;
        Psi_Zero_Inv : constant T_Ref := 1175;

        type Index_Ref is range 0 .. 255;

        type Array_Zq is array (Index_Ref range <>) of T_Ref;

        type Poly_Zq_Ref is array (Index_Ref) of T_Ref;
        type NTT_Poly_Zq_Ref is array (Index_Ref) of T_Ref;

        function To_Big (A : Index_Ref) return Big_Natural
        is
            (To_Big_Integer (Integer (A)));

        function "**" (A : T_Ref;
                       B : Big_Natural) return T_Ref
            with Post => "**"'Result = (if B = 0 then 1 else A * (A ** (B - 1))),
                 Subprogram_Variant => (Decreases => B);

        function "**" (A : T_Ref ;
                       B : Big_Natural) return T_Ref
        is
            (if B = 0 then 1 else A * (A ** (B - 1)));

    end ZqRef;

    use ZqRef;


   package Generic_Sum is new Sum_On_Array (T_Ref, Index_Ref, Array_Zq);

   function NTT_Very_Inner_Ref (E : Array_Zq; Psi : T_Ref; J : Index_Ref; I : Index_Ref) return T_Ref 
      with Pre => (I in E'Range),
           Post => NTT_Very_Inner_Ref'Result = Psi ** (2 * To_Big (I) * To_Big (J) + To_Big (I) ) * E (I);

   function Array_Generator_Very_Inner is new Generic_Sum.InitialArray (NTT_Very_Inner_Ref);

   function NTT_Inner_Ref (E : Array_Zq; Psi : T_Ref; Useless : Index_Ref; J : Index_Ref) return T_Ref
      with Post => NTT_Inner_Ref'Result = Generic_Sum.Sum (Array_Generator_Very_Inner (E, Psi, J));

   function Array_Generator_Inner is new Generic_Sum.InitialArray (NTT_Inner_Ref);

    function NTT_Ref (E : Array_Zq;
                      Psi : T_Ref) return Array_Zq
        with Pre => ((E'First = 0 and E'Last >= E'First and E'Length <= Integer (Index_Ref'Last + 1))) and then
                    (E'Length = 1 or Is_Pow_Of_Two (E'Length)),
             Post => NTT_Ref'Result'First = E'First and NTT_Ref'Result'Last = E'Last and
                     NTT_Ref'Result = Array_Generator_Inner (E, Psi, 0);

end RefMLKEM;