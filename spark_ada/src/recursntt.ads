--  This is an intermediate implementation of the NTT with divide and conquer

with RefMLKEM; use RefMLKEM.ZqRef;
with SumGen; use SumGen;

package RecursNTT
    with SPARK_Mode => On
is

    type Array_Of_Zq is array (Index_Ref range <>) of T_Ref;

    --  This function is meant to be recursive
    function NTT_Recurs (E : Array_Of_Zq;
                         Psi : T_Ref) return Array_Of_Zq
        with Pre => ((E'First = 0 and E'Last > E'First and E'Length <= Integer (Index_Ref'Last + 1))) and then
                    (E'Length = 1 or Is_Pow_Of_Two (E'Length));

end RecursNTT;