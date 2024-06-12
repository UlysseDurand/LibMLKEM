
with SPARK.Big_Integers; use SPARK.Big_Integers;
with SumGen;

package RefMLKEM
    with SPARK_Mode => On
is

    package ZqRef 
        with SPARK_Mode => On
    is

        Q : constant := 3329;

        type T_Ref is mod Q;

        Psi : constant T_Ref := 17;
        Psi_Inv : constant T_Ref := 1175;

        type Index_Ref is range 0 .. 255;

        function Index_Ref_To_Big (A : Index_Ref) return Big_Integer
        is
            (To_Big_Integer (Integer (A)));

        type Poly_Zq_Ref is array (Index_Ref) of T_Ref;
        type NTT_Poly_Zq_Ref is array (Index_Ref) of T_Ref;

        function To_Big (A : Index_Ref) return Big_Natural
        is
            (To_Big_Integer (Integer (A)));

        function "**" (A : T_Ref ;
                       B : Big_Natural) return T_Ref
            with Subprogram_Variant => (Decreases => B);

        function "**" (A : T_Ref ;
                       B : Big_Natural) return T_Ref
        is
            (if B = 0 then 1 else A * (A ** (B - 1)));

    end ZqRef;

    use ZqRef;

   function NTT_Ref (A : in Poly_Zq_Ref) return NTT_Poly_Zq_Ref;

end RefMLKEM;