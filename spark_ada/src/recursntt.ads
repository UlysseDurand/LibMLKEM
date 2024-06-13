--  This is an intermediate implementation of the NTT with divide and conquer

with RefMLKEM; use RefMLKEM.ZqRef;

package RecursNTT
    with SPARK_Mode => On
is


    --  This function is meant to be recursive
    generic
        type IndexRange is range <>;
        type ArrayType is array (IndexRange) of T_Ref;
    package Generic_NTT_Recurs is
        Length : Integer := Integer (IndexRange'Last) + 1;

        function NTT_Recurs (E : ArrayType;
                             Psi : T_Ref) return ArrayType;
    end Generic_NTT_Recurs;

end RecursNTT;