--  This is an intermediate implementation of the NTT with divide and conquer

with RefMLKEM; use RefMLKEM.ZqRef;
with SumGen; use SumGen;

package RecursNTT
    with SPARK_Mode => On
is

    --  This function is meant to be recursive
    function NTT_Recurs (E : Poly_Zq_Ref;
                         Psi : T_Ref;
                         Length : Positive) return NTT_Poly_Zq_Ref
        with Pre => Length <= Integer (Index_Ref'Last + 1) and
                    Is_Pow_Of_Two (Length);

end RecursNTT;