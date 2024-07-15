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
             Post => NTT_Recurs'Result'First = E'First and NTT_Recurs'Result'Last = E'Last and (
                     if (E'Length = 1) then 
                        NTT_Recurs'Result (0) = E (0) 
                     else 
                        (for all J_Dex in 0 .. Index_Ref (E'Length / 2) - 1 => (
                            NTT_Recurs'Result (J_Dex) = 
                                NTT_Recurs (Generic_Sum.Extract_Even (E), Square (E, Psi)) (J_Dex) + 
                                Psi ** (2 * To_Big (J_Dex)) * NTT_Recurs (Generic_Sum.Extract_Odd (E), Square (E, Psi)) (J_Dex) and
                            NTT_Recurs'Result (J_Dex + Index_Ref (E'Length / 2)) = 
                                NTT_Recurs (Generic_Sum.Extract_Even (E), Square (E, Psi)) (J_Dex) - 
                                Psi ** (2 * To_Big (J_Dex)) * NTT_Recurs (Generic_Sum.Extract_Odd (E), Square (E, Psi)) (J_Dex)
                        ))
                     ),
             Subprogram_Variant => (Decreases => E'Length),
             Annotate => (GNATprove, Always_Return);

    function Square (E : Array_Zq ; Psi : T_Ref) return T_Ref
        with Pre => Psi ** (To_Big_Integer (E'Length)) = - 1,
            Post => Square'Result = Psi ** (To_Big_Integer (2)) and
                    Square'Result ** (To_Big_Integer (E'Length / 2)) = -1;

    function Square (E : Array_Zq ; Psi : T_Ref) return T_Ref
    is 
        (Psi ** (To_Big_Integer (2)));

    function Lemma_Recurs_Equiv_Ref (E : Array_Zq ; Psi : T_Ref) return Boolean
        with Pre => ((Psi ** To_Big_Integer (E'Length) = - 1) and
                    (E'First = 0 and E'Length > 0)) and then (
                    Is_Pow_Of_Two (E'Length)), 
            Post => Lemma_Recurs_Equiv_Ref'Result and NTT_Recurs (E, Psi) = NTT_Ref (E, Psi),
             Subprogram_Variant => (Decreases => E'Length),
             Annotate => (GNATprove, Always_Return);

    procedure rewrite1 (E : Array_Zq; E_Even : Array_Zq; Psi : T_Ref; Psi_Square : T_Ref; J_Dex : Index_Ref; I_Dex : Index_Ref; J_Big : Big_Integer ; I_Big : Big_Integer)
        with Pre => ( 
                I_Dex in E_Even'Range and
                2 * I_Dex in E'Range) and then (
                    E_Even (I_Dex) = E (2 * I_Dex) and
                    Psi_Square = Psi ** (To_Big_Integer (2)) and
                    J_Big = To_Big (J_Dex) and I_Big = To_Big (I_Dex)
                ),
            Post => NTT_Very_Inner_Ref (E_Even, Psi_Square, J_Dex, I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex, 2 * I_Dex);

    procedure rewrite2 (E : Array_Zq; E_Odd : Array_Zq; Psi : T_Ref; Psi_Square : T_Ref; J_Dex : Index_Ref; I_Dex : Index_Ref; J_Big : Big_Integer ; I_Big : Big_Integer)
        with Pre => (
                I_Dex in E_Odd'Range and
                2 * I_Dex + 1 in E'Range) and then (
                    E_Odd (I_Dex) = E (2 * I_Dex + 1) and
                    Psi_Square = Psi ** (To_Big_Integer (2)) and
                    J_Big = To_Big (J_Dex) and I_Big = To_Big (I_Dex)
                ),
            Post => Psi ** (2 * J_Big + 1) * NTT_Very_Inner_Ref (E_Odd, Psi_Square, J_Dex, I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex, 2 * I_Dex + 1);

    procedure rewrite3 (E : Array_Zq; E_Even : Array_Zq; Psi : T_Ref; Psi_Square : T_Ref; Mid_Dex : Index_Ref ; J_Dex : Index_Ref; I_Dex : Index_Ref; Mid_Big : Big_Integer ; J_Big : Big_Integer ; I_Big : Big_Integer)
        with Pre => (
                I_Dex in E_Even'Range and
                J_Dex + Mid_Dex in E'Range and
                Psi ** To_Big_Integer (E'Length) = -1 and
                2 * I_Dex in E'Range) and then (
                    E_Even (I_Dex) = E (2 * I_Dex) and
                    Psi_Square = Psi ** To_Big_Integer (2) and
                    J_Big = To_Big (J_Dex) and I_Big = To_Big (I_Dex) and Mid_Big = To_Big (Mid_Dex) and
                    2 * Mid_Big = To_Big_Integer (E'Length)
                ),
            Post => NTT_Very_Inner_Ref (E_Even, Psi_Square, J_Dex, I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex + Mid_Dex, 2 * I_Dex);

    procedure rewrite4 (E : Array_Zq; E_Odd : Array_Zq; Psi : T_Ref; Psi_Square : T_Ref; Mid_Dex : Index_Ref ; J_Dex : Index_Ref; I_Dex : Index_Ref; Mid_Big : Big_Integer ; J_Big : Big_Integer ; I_Big : Big_Integer)
        with Pre => ( 
                I_Dex in E_Odd'Range and
                J_Dex + Mid_Dex in E'Range and
                Psi ** To_Big_Integer (E'Length) = -1 and
                2 * I_Dex + 1 in E'Range) and then (
                    E_Odd (I_Dex) = E (2 * I_Dex + 1) and
                    Psi_Square = Psi ** To_Big_Integer (2) and
                    J_Big = To_Big (J_Dex) and I_Big = To_Big (I_Dex) and Mid_Big = To_Big (Mid_Dex) and
                    2 * Mid_Big = To_Big_Integer (E'Length)
                ),
            Post => (- Psi ** (2 * J_Big + 1)) * NTT_Very_Inner_Ref (E_Odd, Psi_Square, J_Dex, I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex + Mid_Dex, 2 * I_Dex + 1);

    procedure rewrite5 (E : Array_Zq ; E_Even : Array_Zq ; Psi :T_Ref ; Psi_Square :T_Ref ; J_Dex :Index_Ref)
        with Pre => (
                Psi ** To_Big_Integer (E'Length) = -1 and
                E'First = 0 and
                E_Even'Length = E'Length / 2 and
                E'Length mod 2 = 0) and then ((
                    Is_Pow_Of_Two (E'Length) and
                    Psi_Square = Square (E, Psi) and
                    E_Even'Last = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex))'Last and
                    E_Even'First = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex))'First )and then (
                        (for all I_Dex in E_Even'Range => (
                            Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex) (I_Dex) = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex)) (I_Dex)
                        )) and
                        J_Dex in E_Even'Range and
                        NTT_Recurs (E_Even, Psi_Square) = NTT_Ref (E_Even, Psi_Square)
                    )
                ),
            Post => NTT_Recurs (E_Even, Psi_Square) (J_Dex) = Generic_Sum.Sum (Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex)));

    procedure rewrite6 (E : Array_Zq ; E_Odd : Array_Zq ; Psi :T_Ref ; Psi_Square :T_Ref ; J_Dex :Index_Ref; B_Bis_J_Array : Array_Zq)
        with Pre => (
                Psi ** To_Big_Integer (E'Length) = -1 and
                E'First = 0 and
                E_Odd'First = 0 and
                E_Odd'Length = E'Length / 2 and
                E'Length mod 2 = 0) and then ((
                    Is_Pow_Of_Two (E'Length) and
                    Psi_Square = Square (E, Psi) and
                    B_Bis_J_Array'Last = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex))'Last and
                    B_Bis_J_Array'First = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex))'First )and then (
                        (for all I_Dex in B_Bis_J_Array'Range => (
                            B_Bis_J_Array (I_Dex) = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex)) (I_Dex)
                        )) and
                        (for all I_Dex in B_Bis_J_Array'Range => ( 
                            B_Bis_J_Array (I_Dex) = Psi ** (2 * To_Big (J_Dex) + 1) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I_Dex)
                        )) and
                        J_Dex in E_Odd'Range and
                        NTT_Recurs (E_Odd, Psi_Square) = NTT_Ref (E_Odd, Psi_Square)
                    )
                ),
            Post => Psi ** (2 * To_Big (J_Dex) + 1) * NTT_Recurs (E_Odd, Psi_Square) (J_Dex) = Generic_Sum.Sum (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex)));



    function Lemma_Index_Ref_Big_Integer_Additive (X : Index_Ref ; Y : Index_Ref) return Boolean
        with Pre => X + Y in Index_Ref,
            Post => Lemma_Index_Ref_Big_Integer_Additive'Result and To_Big (X + Y) = To_Big (X) + To_Big (Y);

    function Lemma_One_Mult_Neutral (X : T_Ref) return Boolean
        with Post => (Lemma_One_Mult_Neutral'Result and 1 * X = X);

    function Lemma_One_Pow_Absorb (X : Big_Natural) return Boolean
        with Post => (Lemma_One_Pow_Absorb'Result and T_Ref (1) ** X = T_Ref (1)),
             Subprogram_Variant => (Decreases => X),
             Annotate => (GNATprove, Always_Return);

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