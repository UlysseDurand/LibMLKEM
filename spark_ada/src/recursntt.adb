with SumGen; use SumGen;
with SPARK.Cut_Operations; use SPARK.Cut_Operations;
with RefMLKEM; use RefMLKEM.ZqRef;
with SPARK.Big_Integers; use SPARK.Big_Integers;

package body RecursNTT
    with SPARK_Mode => On
is



    function NTT_Recurs (E : Array_Zq;
                         Psi : T_Ref) return Array_Zq
    is
        Res : Array_Zq (0 .. Index_Ref (E'Length - 1)) with Relaxed_Initialization;
    begin
        if E'Length = 1 then
            Res (0) := E (0);
        else
            declare 
                Num_Mid : Integer := E'Length / 2;
                Mid_Dex : Index_Ref := Index_Range (Num_Mid); 
                E_Even : Array_Zq (0 .. Mid_Dex) := Generic_Sum.Extract_Even (E);
                E_Odd : Array_Zq (0 .. Mid_Dex) := Generic_Sum.Extract_Odd (E);
                Psi_Square : T_Ref := Psi * Psi;
                A_Recurs : Array_Zq (0 .. Mid_Dex) := NTT_Recurs (E_Even, Psi_Square);
                B_Recurs : Array_Zq (0 .. Mid_Dex) := NTT_Recurs (E_Odd, Psi_Square);
                A_Ref : Array_Zq (0 .. Mid_Dex) := NTT_Ref (E_Even, Psi_Square);
                B_Ref : Array_Zq (0 .. Mid_Dex) := NTT_Ref (E_Odd, Psi_Square);
                B_Bis : Array_Zq (A_Recurs'Range) with Relaxed_Initialization; 
            begin
                for J in 0 .. Num_Mid - 1 loop
                    declare
                        J_Dex : Index_Ref := Index_Ref (J);
                        begin
                            B_Bis (J_Dex) := Psi ** (2 * J + 1) * B_Recurs (J_Dex);
                        end;
                end loop;
                pragma Assume (B_Bis'Initialized);

                pragma Assert (A_Recurs = A_Ref);
                pragma Assert (B_Recurs = B_Ref);

                for J in 0 .. Num_Mid - 1 loop

                    Res (J_Dex) := A_Recurs (J_Dex) + Psi ** (2 * J + 1) * B_Recurs (J_Dex);
                    Res (J_Dex + Mid_Dex) := A_Recurs (J_Dex) - Psi ** (2 * J + 1) * B_Recurs (J_Dex);
                    -- Then we have to prove that Res (J) = The right expression

                    declare
                        J_Dex : Index_Ref := Index_Ref (J);
                        J_Bis : T_Ref := J + Num_Mid;

                        AJ_Recurs_Sum_Term : Array_Zq (0 .. Mid_Dex);
                        BJ_Recurs_Sum_Term : Array_Zq (0 .. Mid_Dex);
                        BJ_Bis_Recurs_Sum_Term : Array_Zq (0 .. Mid_Dex);
                    begin
                        for I in 0 .. Mid_Dex loop
                            declare
                                I_Dex : Index_Ref := Index_Ref (I);
                            begin
                            end;
                        end loop;

                        for I in 0 .. Mid_Dex loop
                            declare
                                I_Dex : Index_Ref := Index_Ref (I);
                            begin
                                pragma Assert (AJ_Recurs_Sum_Term (I_Dex) = Psi_Square ** (2 * I * J + I) * E_Even (I_Dex));
                                pragma Assert (AJ_Recurs_Sum_Term (I_Dex) = Psi ** (4 * I * J + 2 * I) * E_Even (I_Dex));
                                pragma Assert (AJ_Recurs_Sum_Term (I_Dex) = Psi ** (2 * To_Even (I) * J + To_Even (I)) * E_Even (I_Dex));

                                pragma Assert (BJ_Recurs_Sum_Term (I_Dex) = Psi_Square ** (2 * I * J + I) * E_Odd (I_Dex));
                                pragma Assert (BJ_Recurs_Sum_Term (I_Dex) = Psi ** (4 * I * J + 2 * I) * E_Odd (I_Dex));
                                pragma Assert (BJ_Bis_Sum_Term (I_Dex) = Psi ** (2 * J + 1) * Psi ** (4 * I * J + 2 * I) * E_Odd(I_Dex));
                                pragma Assert (BJ_Bis_Sum_Term (I_Dex) = Psi ** (4 * U * J + 2 * I + 2 * J + 1) * E_Odd (I_Dex));
                                pragma Assert (BJ_Bis_Sum_Term (I_Dex) = Psi ** (2 * To_Odd (I) * J + To_Odd (I)) * E_Odd (I_Dex));
                            end;
                        end loop;

                        pragma Assert (A_Recurs (J_Dex) = Generic_Sum.Sum (AJ_Recurs_Sum_Term));
                        pragma Assert (B_Recurs (J_Dex) = Generic_Sum.Sum (BJ_Recurs_Sum_Term));
                        pragma Assert (B_Bis (J_Dex) = Generic_Sum.Sum (BJ_Bis_Sum_Term));

                        pragma Assert (Res (J_Dex) = A_Recurs (J_Dex) + Psi ** (2 * J + 1) * B_Recurs (J_Dex));
                        pragma Assert (Res (J_Dex + Mid_Dex) = A_Recurs (J_Dex) - Psi ** (2 * J + 1) * B_Recurs (J_Dex));

                        pragma Assert (By (
                            A_Recurs (J_Dex) - Psi ** (2 * J + 1) * B_Recurs (J_Dex) = A_Recurs (J_Dex) + (-1) * (Psi ** (2 * J + 1) * B_Recurs (J_Dex)),
                            Lemma_Minus_Factor (A_Recurs (J_Dex), Psi ** (2 * J + 1) * B_Recurs (J_Dex))
                        ));
                        pragma Assert (By (
                            Res (J_Dex + Mid_Dex) = A_Recurs (J_Dex) + (-1) * Psi ** (2 * J + 1) * B_Recurs (J_Dex), 
                            Lemma_Mult_Associative (-1, Psi ** (2 * J + 1), B_Recurs (J_Dex))
                        ));
                        pragma Assert (Res (J_Dex + Mid_Dex) = A_Recurs (J_Dex) + (Psi ** (E'Length) * Psi ** (2 * J + 1) * B_Recurs (J_Dex)));
                        pragma Assert (By (
                            Res (J_Dex + Mid_Dex) = A_Recurs (J_Dex) + (Psi ** (E'Length + 2 * J + 1) * B_Recurs (J_Dex)), 
                            Lemma_Pow_Additive (Psi, E'Length, 2 * J + 1)
                        ));
                        pragma Assert (Res (J_Dex + Mid_Dex) = A_Recurs (J_Dex) + (Psi_Square ** (Num_Mid + J + 1) * B_Recurs (J_Dex)));

                        -- Res (J)
                        -- = \sum n/2 | (psi^2)^(2ij+i) * e_even(i) + psi^(2j+1) \sum n/2 | (psi^2)^(2ij+i) * e_odd(i)   === A_Ref | B_Ref
                        -- = \sum n/2 | psi^(4ij+2i) * e_even(i) + psi^(2j+1) \sum n/2 | psi^(4ij+2i) * e_odd(i)         === A_Ref | B_Ref
                        -- = \sum n/2 | psi^(4ij+2i) * e_even(i) + \sum n/2 | psi^(4ij+2j+2i+1) * e_odd(i)               === A_Ref | BJ_Bis
                        -- = \sum n/2 | psi^(4ij+2i) * e (2i) + \sum n/2 | psi^(4ij+2j+2i+1) * e (2i+1)                  === A_Ref | BJ_Bis
                        -- = \sum n/2 | psi^(2(2i)j+(2i)) * e_even (i) + \sum n/2 | psi^(2(2i+1)j+(2i+1)) * e_odd (i)    === A_Ref | BJ_Bis
                        --   \sum n | psi^(2ij+i) * e (i)                                                                === Res

                    end;
                    
                end loop;
                pragma Assume (for all J in 0 .. (E'Length - 1) => Res (Index_Ref (J))'Initialized);
            end;
        end if;
        return Res;
    end NTT_Recurs;

    function Lemma_Minus_Factor (X : T_Ref;
                                 Y : T_Ref) return Boolean
    is
        Z1 : T_Ref := X - Y;
        Z2 : T_Ref := X + (-1) * Y;
    begin
        pragma Assume (Z1 = Z2);
        return True;
    end Lemma_Minus_Factor;

    function Lemma_Mult_Associative (X : T_Ref;
                                     Y : T_Ref;
                                     Z : T_Ref) return Boolean
    is
    begin
        pragma Assume ((X * Y) * Z = X * (Y * Z));
        return True;
    end Lemma_Mult_Associative;

    function Lemma_Pow_Additive (X : T_Ref;
                                 A : Integer;
                                 B : Integer) return Boolean
    is 
    begin
        pragma Assume (X ** (A + B) = (X ** A) * (X ** B));
        return True;
    end Lemma_Pow_Additive;


end RecursNTT;