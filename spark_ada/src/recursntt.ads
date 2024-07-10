--  This is an intermediate implementation of the NTT with divide and conquer

with RefMLKEM; use RefMLKEM.ZqRef; use RefMLKEM;
with SumGen; use SumGen;
with SPARK.Big_Integers; use SPARK.Big_Integers;

package RecursNTT
    with SPARK_Mode => On
is

    --  This function is meant to be recursive
    function NTT_Recurs (E : Array_Zq;
                         Psi : T_Ref) return Array_Zq
        with Pre => (Psi ** To_Big_Integer (E'Length) = - 1 and
                    (E'First = 0 and E'Last >= E'First and E'Length <= Integer (Index_Ref'Last + 1))) and then  
                    (Is_Pow_Of_Two (E'Length)),
             Post => NTT_Recurs'Result'First = E'First and NTT_Recurs'Result'Last = E'Last and
                     NTT_Recurs'Result = NTT_Ref (E, Psi),
             Subprogram_Variant => (Decreases => E'Length),
             Annotate => (GNATprove, Always_Return);

    procedure rewrite1 (E : Array_Zq; E_Even : Array_Zq; Psi : T_Ref; Psi_Square : T_Ref; J_Dex : Index_Ref; I_Dex : Index_Ref; J_Big : Big_Integer ; I_Big : Big_Integer ; A_J_Very_Inner : Array_Zq)
        with Pre => 
                    (E'First = 0 and 
                    E'Length mod 2 = 0 and
                    E'Length > 1) and then ((
                    I_Dex in E_Even'Range and
                    I_Dex in A_J_Very_Inner'Range and
                    2 * I_Dex in E'Range) and then (
                    E_Even = Generic_Sum.Extract_Even (E) and
                    Psi_Square = Psi ** (To_Big_Integer (2)) and
                    J_Big = To_Big (J_Dex) and I_Big = To_Big (I_Dex) and
                    A_J_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E_Even, Psi_Square, J_Dex, I_Dex)
                    )),
             Post => A_J_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex, 2 * I_Dex);

    procedure rewrite2 (E : Array_Zq; E_Odd : Array_Zq; Psi : T_Ref; Psi_Square : T_Ref; J_Dex : Index_Ref; I_Dex : Index_Ref; J_Big : Big_Integer ; I_Big : Big_Integer ; B_Bis_J_Very_Inner : Array_Zq ; B_J_Very_Inner : Array_Zq)
        with Pre => 
                    (E'First = 0 and 
                    E'Length mod 2 = 0 and
                    E'Length > 1) and then ((
                    I_Dex in E_Odd'Range and
                    I_Dex in B_J_Very_Inner'Range and
                    I_Dex in B_Bis_J_Very_Inner'Range and
                    I_Big >= 0 and J_Big >= 0 and
                    2 * I_Dex in E'Range) and then (
                    E_Odd = Generic_Sum.Extract_Odd (E) and
                    Psi_Square = Psi ** (To_Big_Integer (2)) and
                    J_Big = To_Big (J_Dex) and I_Big = To_Big (I_Dex) and
                    B_J_Very_Inner (I_Dex) = Psi ** (4 * I_Big * J_Big + 2 * I_Big) * E_Odd (I_Dex) and
                    B_Bis_J_Very_Inner (I_Dex) = Psi ** (2 * J_Big + 1) * B_J_Very_Inner (I_Dex)
                    )),
             Post => B_Bis_J_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex, 2 * I_Dex + 1);

    procedure rewrite3 (E : Array_Zq; E_Even : Array_Zq; Psi : T_Ref; Psi_Square : T_Ref; Mid_Dex : Index_Ref ; J_Dex : Index_Ref; I_Dex : Index_Ref; Mid_Big : Big_Integer ; J_Big : Big_Integer ; I_Big : Big_Integer ; A_J_Plus_Mid_Very_Inner : Array_Zq)
        with Pre => 
                    (E'First = 0 and 
                    E'Length mod 2 = 0 and
                    E'Length > 1) and then ((
                    Mid_Big = To_Big (Mid_Dex) and
                    I_Dex in E_Even'Range and
                    I_Dex in A_J_Plus_Mid_Very_Inner'Range and
                    J_Dex + Mid_Dex in E'Range and
                    2 * I_Dex in E'Range) and then (
                    E_Even = Generic_Sum.Extract_Even (E) and
                    Psi_Square = Psi ** (To_Big_Integer (2)) and
                    J_Big = To_Big (J_Dex) and I_Big = To_Big (I_Dex) and Mid_Big = To_Big (Mid_Dex) and
                    A_J_Plus_Mid_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E_Even, Psi_Square, J_Dex + Mid_Dex, I_Dex)
                    )),
             Post => A_J_Plus_Mid_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex + Mid_Dex, 2 * I_Dex);

    procedure rewrite3bis (E : Array_Zq; E_Odd : Array_Zq; Psi : T_Ref; Psi_Square : T_Ref; Mid_Dex : Index_Ref ; J_Dex : Index_Ref; I_Dex : Index_Ref; Mid_Big : Big_Integer ; J_Big : Big_Integer ; I_Big : Big_Integer ; B_Bis_J_Plus_Mid_Very_Inner : Array_Zq ; B_J_Plus_Mid_Very_Inner : Array_Zq)
        with Pre => 
                    (E'First = 0 and 
                    E'Length mod 2 = 0 and
                    E'Length > 1) and then ((
                    I_Dex in E_Odd'Range and
                    I_Dex in B_J_Plus_Mid_Very_Inner'Range and
                    I_Dex in B_Bis_J_Plus_Mid_Very_Inner'Range and
                    J_Dex + Mid_Dex in E'Range and
                    I_Big >= 0 and J_Big >= 0 and Mid_Big >=0 and
                    2 * I_Dex + 1 in E'Range) and then (
                    E_Odd = Generic_Sum.Extract_Odd (E) and
                    Psi_Square = Psi ** (To_Big_Integer (2)) and
                    J_Big = To_Big (J_Dex) and I_Big = To_Big (I_Dex) and Mid_Big = To_Big (Mid_Dex) and
                    B_J_Plus_Mid_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E_Odd, Psi_Square, J_Dex + Mid_Dex, I_Dex)
                    )),
             Post => B_J_Plus_Mid_Very_Inner (I_Dex) = Psi ** (4 * I_Big * J_Big + 2 * I_Big) * E_Odd (I_Dex);

    procedure rewrite4 (E : Array_Zq; E_Odd : Array_Zq; Psi : T_Ref; Psi_Square : T_Ref; Mid_Dex : Index_Ref ; J_Dex : Index_Ref; I_Dex : Index_Ref; Mid_Big : Big_Integer ; J_Big : Big_Integer ; I_Big : Big_Integer ; B_Bis_J_Plus_Mid_Very_Inner : Array_Zq ; B_J_Plus_Mid_Very_Inner : Array_Zq)
        with Pre =>
                    (E'First = 0 and 
                    E'Length mod 2 = 0 and
                    E'Length > 1) and then ((
                    I_Dex in E_Odd'Range and
                    I_Dex in B_J_Plus_Mid_Very_Inner'Range and
                    I_Dex in B_Bis_J_Plus_Mid_Very_Inner'Range and
                    J_Dex + Mid_Dex in E'Range and
                    I_Big >= 0 and J_Big >= 0 and
                    2 * I_Dex in E'Range) and then (
                    E_Odd = Generic_Sum.Extract_Odd (E) and
                    2 * Mid_Big = To_Big_Integer (E'Length) and
                    Psi_Square = Psi ** (To_Big_Integer (2)) and
                    -1 = Psi ** To_Big_Integer (E'Length) and
                    J_Big = To_Big (J_Dex) and I_Big = To_Big (I_Dex) and
                    B_J_Plus_Mid_Very_Inner (I_Dex) = Psi ** (4 * I_Big * J_Big + 2 * I_Big) * E_Odd (I_Dex) and
                    B_Bis_J_Plus_Mid_Very_Inner (I_Dex) = (- Psi ** (2 * J_Big + 1)) * B_J_Plus_Mid_Very_Inner (I_Dex)
                    )),
             Post => B_Bis_J_Plus_Mid_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex + Mid_Dex, 2 * I_Dex + 1); 

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
                                 A : Big_Integer;
                                 B : Big_Integer) return Boolean
        with Pre => A >=0 and B >= 0,
             Post => Lemma_Pow_Additive'Result and
                     (X ** A) * (X ** B) = X ** (A + B);

    function Lemma_Pow_Mult (X : T_ref;
                             A : Big_Integer;
                             B : Big_Integer) return Boolean
        with Pre => A >= 0 and B >= 0,
             Post => Lemma_Pow_Mult'Result and
                     ((X ** A) ** B = X ** (A * B));

end RecursNTT;