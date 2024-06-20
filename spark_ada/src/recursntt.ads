--  This is an intermediate implementation of the NTT with divide and conquer

with RefMLKEM; use RefMLKEM.ZqRef; use RefMLKEM;
with SumGen; use SumGen;
with SPARK.Big_Integers; use SPARK.Big_Integers;

package RecursNTT
    with SPARK_Mode => On
is

    package Generic_Sum is new Sum_On_Array (T_Ref, Index_Ref, Array_Zq);

    --  This function is meant to be recursive
    function NTT_Recurs (E : Array_Zq;
                         Psi : T_Ref) return Array_Zq
        with Pre => (Psi ** E'Length / 2 = -1 and
                    (E'First = 0 and E'Last >= E'First and E'Length <= Integer (Index_Ref'Last + 1))) and then  
                    (E'Length = 1 or Is_Pow_Of_Two (E'Length)),
             Post => NTT_Recurs'Result'First = E'First and NTT_Recurs'Result'Last = E'Last;

    function Lemma_Minus_Factor (X : T_Ref;
                                 Y : T_Ref) return Boolean
        with Post => Lemma_Minus_Factor'Result and
                     (X - Y = X + (-1) * Y);

    function Lemma_Mult_Associative (X : T_Ref;
                                     Y : T_Ref;
                                     Z : T_Ref) return Boolean
        with Post => Lemma_Mult_Associative'Result and
                     (X * Y) * Z = X * (Y * Z);

    function Lemma_Pow_Additive (X : T_Ref;
                                 A : Integer;
                                 B : Integer) return Boolean
        with Pre => A >=0 and B >= 0 and A < Integer'Last / 2 and B < Integer'Last / 2, 
             Post => Lemma_Pow_Additive'Result and
                     (X ** A) * (X ** B) = X ** (A + B);

end RecursNTT;