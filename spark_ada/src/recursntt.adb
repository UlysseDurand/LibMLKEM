with SumGen; use SumGen;
with SPARK.Cut_Operations; use SPARK.Cut_Operations;
with RefMLKEM; use RefMLKEM.ZqRef;
use RefMLKEM;
with SPARK.Big_Integers; use SPARK.Big_Integers;

package body RecursNTT
    with SPARK_Mode => On
is

    function NTT_Recurs (E : Array_Zq;
                         Psi : T_Ref) return Array_Zq
    is
        Res : Array_Zq (E'Range) with Relaxed_Initialization;

        Goal : Array_Zq (E'Range) := NTT_Ref (E, Psi);
    begin
        if E'Length = 1 then
            Res (0) := E (0);
            pragma Assert (NTT_Very_Inner_Ref (E, Psi, 0, 0) = E (0));
            pragma Assert (Array_Generator_Very_Inner (E, Psi, 0) (0) = E (0));
            pragma Assert (Generic_Sum.Cut_Last (Array_Generator_Inner (E, Psi, 0))'Length = 0);
            pragma Assert (Generic_Sum.Sum (Generic_Sum.Cut_Last (Array_Generator_Inner (E, Psi, 0))) = 0);
            pragma Assert (Generic_Sum.Sum (Array_Generator_Very_Inner (E, Psi, 0)) = E (0));
            pragma Assert (NTT_Inner_Ref (E, Psi, 0, 0)  = E (0));
            pragma Assert (Goal (0) = E (0));
            pragma Assert (Res = Goal);
        else
            declare
                pragma Assert (E'Length mod 2 = 0);
                E_Even : Array_Zq (0 .. E'Length / 2 - 1) := Generic_Sum.Extract_Even (E);
                E_Odd : Array_Zq (0 .. E'Length / 2 - 1) := Generic_Sum.Extract_Odd (E);
                Psi_Square : T_Ref := Psi ** To_Big_Integer (2);
                pragma Assert (By(
                    Psi_Square ** (To_Big_Integer (E'Length / 2)) = Psi ** (To_Big_Integer (E'Length)),
                    Lemma_Pow_Mult (Psi, To_Big_Integer (2), To_Big_Integer (E'Length / 2))
                ));
                pragma Assert (Psi_Square ** To_Big_Integer (E_Even'Length) = - 1);
                pragma Assert (Is_Pow_Of_Two (E_Even'Length));
                pragma Assert (E_Odd'Length mod 2 = 0 or E_Odd'Length = 1);
                A_Recurs : Array_Zq (E_Even'Range) := NTT_Recurs (E_Even, Psi_Square);
                B_Recurs : Array_Zq (E_Odd'Range) := NTT_Recurs (E_Odd, Psi_Square);
                A_Ref : Array_Zq (E_Even'Range) := NTT_Ref (E_Even, Psi_Square);
                B_Ref : Array_Zq (E_Odd'Range) := NTT_Ref (E_Odd, Psi_Square);
                B_Bis : Array_Zq (A_Recurs'Range) with Relaxed_Initialization; 
                B_Bis_Minus : Array_Zq (A_Recurs'Range) with Relaxed_Initialization;

                Num_Mid : Integer := E'Length / 2;
                Mid_Dex : Index_Ref := Index_Ref (Num_Mid); 
                Mid_Big : Big_Integer := To_Big (Mid_Dex);
            begin
                pragma Assume (B_Bis'Initialized);

                pragma Assert (A_Recurs = A_Ref);
                pragma Assert (B_Recurs = B_Ref);

                pragma Assert (A_Ref = Array_Generator_Inner (E_Even, Psi_Square, 0));
                pragma Assert (for all J_Dex in E_Even'Range => (A_Ref (J_Dex) = NTT_Inner_Ref (E_Even, Psi_Square, 0, J_Dex)));

                pragma Assert (B_Ref = Array_Generator_Inner (E_Odd, Psi_Square, 0));
                pragma Assert (for all J_Dex in E_Odd'Range => (B_Ref (J_Dex) = NTT_Inner_Ref (E_Odd, Psi_Square, 0, J_Dex)));

                for J in 0 .. Num_Mid - 1 loop
                    declare
                        J_Dex : Index_Ref := Index_Ref (J);
                        J_Bis : T_Ref := T_Ref (J + Num_Mid);
                        J_Big : Big_Integer := To_Big (J_Dex);

                        A_J_Very_Inner : Array_Zq (E_Even'Range) := Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex);
                        B_J_Very_Inner : Array_Zq (E_Odd'Range) := Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex);
                        B_Bis_Very_Inner : Array_Zq (E_Odd'Range) := Generic_Sum.Scalar_Mult (Psi ** (2 * J_Big + 1), B_J_Very_Inner);
                        B_Bis_Minus_Very_Inner : Array_Zq (E_Odd'Range) := Generic_Sum.Scalar_Mult (- Psi ** (2 * J_Big + 1), B_J_Very_Inner);

                        A_J_Plus_Mid_Very_Inner : Array_Zq (E_Even'Range) := Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex);
                        B_J_Plus_Mid_Very_Inner : Array_Zq (E_Odd'Range) := Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex);

                        Big_Array : Array_Zq (E'Range) := Array_Generator_Very_Inner (E, Psi, J_Dex);
                        Big_Array_Plus_Mid : Array_Zq (E'Range) := Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex);
                    begin
                        pragma Assert (J_Dex in E_Even'Range);
                        pragma Assert (A_Ref (J_Dex) = NTT_Inner_Ref (E_Even, Psi_Square, 0, J_Dex));

                        pragma Assert (J_Dex in E_Odd'Range);
                        pragma Assert (B_Ref (J_Dex) = NTT_Inner_Ref (E_Odd, Psi_Square, 0, J_Dex));

                        --  B_Bis (J_Dex) := Psi ** (2 * J_Big + 1) * B_Recurs (J_Dex);


                        for I in 0 .. Num_Mid - 1 loop
                            declare
                                I_Dex : Index_Ref := Index_Ref (I);
                                I_Big : Big_Integer := To_Big (I_Dex);
                            begin
                                -- We start with A_J_Very_Inner, the sum expression for A_Ref at indices J, I
                                -- And we want to prove that it equals Big_Array (2 * I)
                                -- Same for B_Bis_J_Very Inner, the sum expression for Psi ** (2 * J + 1) times B_Ref at indices J, I

                                    pragma Assert (By(
                                        (Psi ** To_Big_Integer (2)) ** (2 * I_Big * J_Big + I_Big) = Psi ** (2 * (2 * I_Big * J_Big + I_Big)), 
                                        Lemma_Pow_Mult (Psi, To_Big_Integer (2), 2 * I_Big * J_Big + I_Big)
                                    ));

                                pragma Assert (A_J_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E_Even, Psi_Square, J_Dex, I_Dex));
                                    pragma Assert (NTT_Very_Inner_Ref (E_Even, Psi_Square, J_Dex, I_Dex) = Psi_Square ** (2 * To_Big (I_Dex) * To_Big (J_Dex) + To_Big (I_Dex)) * E_Even (I_Dex));
                                    pragma Assert (A_J_Very_Inner (I_Dex) = Psi_Square ** (2 * I_Big * J_Big + I_Big) * E_Even (I_Dex));
                                    pragma Assert (A_J_Very_Inner (I_Dex) = Psi ** (2 * (2 * I_Big * J_Big + I_Big)) * E_Even (I_Dex));
                                    pragma Assert (A_J_Very_Inner (I_Dex) = Psi ** (2 * (2 * I_Big) * J_Big + (2 * I_Big)) * E_Even (I_Dex));
                                    pragma Assert (E_Even (I_Dex) = E (2 * I_Dex));
                                    pragma Assert (A_J_Very_Inner (I_Dex) = Psi ** (2 * (2 * I_Big) * J_Big + (2 * I_Big)) * E (2 * I_Dex));
                                    pragma Assert (Psi ** (2 * (2 * I_Big) * J_Big + (2 * I_Big)) * E (2 * I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex, 2 * I_Dex));
                                    pragma Assert (A_J_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex, 2 * I_Dex));
                                pragma Assert (A_J_Very_Inner (I_Dex) = Big_Array (2 * I_Dex));

                                pragma Assert (B_J_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E_Odd, Psi_Square, J_Dex, I_Dex));
                                    pragma Assert (B_J_Very_Inner (I_Dex) = Psi_Square ** (2 * I_Big * J_Big + I_Big) * E_Odd (I_Dex));
                                    pragma Assert (B_J_Very_Inner (I_Dex) = Psi ** (4 * I_Big * J_Big + 2 * I_Big) * E_Odd (I_Dex));

                                pragma Assert (B_Bis_Very_Inner (I_Dex) = Psi ** (2 * J_Big + 1) * B_J_Very_Inner (I_Dex));
                                    -- ...
                                    pragma Assert (B_Bis_Very_Inner (I_Dex) = (Psi ** (2 * J_Big + 1)) * (Psi ** (4 * I_Big * J_Big + 2 * I_Big) * E_Odd (I_Dex)));
                                    pragma Assert (By(
                                        Psi ** (2 * J_Big + 1) * Psi ** (4 * I_Big * J_Big + 2 * I_Big) = Psi ** (2 * J_Big + 1 + 4 * I_Big  * J_Big + 2 * I_Big), 
                                        Lemma_Pow_Additive (Psi, 2 * J_Big + 1, 4 * I_Big * J_Big + 2 * I_Big)
                                    ));
                                    pragma Assert (B_Bis_Very_Inner (I_Dex) = Psi ** (4 * I_Big * J_Big + 2 * I_Big + 2 * J_Big + 1) * E_Odd (I_Dex));
                                    pragma Assert (B_Bis_Very_Inner (I_Dex) = Psi ** (2 * (2 * I_Big + 1) * J_Big + (2 * I_Big + 1)) * E_Odd (I_Dex));
                                    pragma Assert (E_Odd (I_Dex) = E (2 * I_Dex + 1));
                                    pragma Assert (B_Bis_Very_Inner (I_Dex) = Psi ** (2 * (2 * I_Big + 1) * J_Big + (2 * I_Big + 1)) * E (2 * I_Dex + 1));
                                    --  pragma Assert (Psi ** (2 * I_Big * J_Big + I_Big) * E (I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex, I_Dex));
                                    pragma Assert (Psi ** (2 * (2 * I_Big + 1) * J_Big + (2 * I_Big + 1)) * E (2 * I_Dex + 1) = NTT_Very_Inner_Ref (E, Psi, J_Dex, 2 * I_Dex + 1));
                                    -- ...
                                    pragma Assert (B_Bis_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex, 2 * I_Dex + 1));
                                pragma Assert (B_Bis_Very_Inner (I_Dex) = Big_Array (2 * I_Dex + 1));

                                -- Now we focus on the J_Dex + Mid_Dex

                                -- We start with A_J_Plus_Mid_Very_Inner, the sum expression for A_Ref at indices J+Mid_Dex, I
                                -- And we want to prove that it equals Big_Array (2 * I)
                                -- Same for B_Bis_J_Plus_Mid_Very Inner, the sum expression for - Psi ** (2 * J + 1) times B_Ref at indices J+Mid_Dex, I

                                    pragma Assert (To_Big (J_Dex + Mid_Dex) = J_Big + Mid_Big);

                                pragma Assert (A_J_Plus_Mid_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E_Even, Psi_Square, J_Dex + Mid_Dex, I_Dex));
                                    pragma Assert (NTT_Very_Inner_Ref (E_Even, Psi_Square, J_Dex + Mid_Dex, I_Dex) = Psi_Square ** (2 * I_Big * (J_Big + Mid_Big) + I_Big) * E_Even (I_Dex));
                                    pragma Assert (By (
                                        (Psi ** To_Big_Integer (2)) ** (2 * I_Big * (J_Big + Mid_Big) + I_Big) = Psi ** (2 * (2 * I_Big * (J_Big + Mid_Big) + I_Big)),
                                        Lemma_Pow_Mult (Psi, To_Big_Integer (2), 2 * I_Big * (J_Big + Mid_Big) + I_Big)
                                    ));
                                    pragma Assert (A_J_Plus_Mid_Very_Inner (I_Dex) = Psi_Square ** (2 * I_Big * (J_Big + Mid_Big) + I_Big) * E_Even (I_Dex));
                                    pragma Assert (A_J_Plus_Mid_Very_Inner (I_Dex) = Psi ** (2 * (2 * I_Big * (J_Big + Mid_Big) + I_Big)) * E_Even (I_Dex));
                                    pragma Assert (A_J_Plus_Mid_Very_Inner (I_Dex) = Psi ** (2 * (2 * I_Big) * (J_Big + Mid_Big) + (2 * I_Big)) * E_Even (I_Dex));
                                    pragma Assert (A_J_Plus_Mid_Very_Inner (I_Dex) = Psi ** (2 * (2 * I_Big) * (J_Big + Mid_Big) + (2 * I_Big)) * E (2 * I_Dex));
                                    pragma Assert (A_J_Plus_Mid_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex + Mid_Dex, 2 * I_Dex));
                                pragma Assert (A_J_Plus_Mid_Very_Inner (I_Dex) = Big_Array_Plus_Mid (2 * I_Dex));


                                pragma Assert (B_J_Plus_Mid_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E_Odd, Psi_Square, J_Dex + Mid_Dex, I_Dex));
                                    pragma Assert (NTT_Very_Inner_Ref (E_Odd, Psi_Square, J_Dex + Mid_Dex, I_Dex) = Psi_Square ** (2 * I_Big * (J_Big + Mid_Big) + I_Big) * E_Odd (I_Dex));
                                    pragma Assert (By (
                                        (Psi ** To_Big_Integer (2)) ** (2 * I_Big * (J_Big + Mid_Big) + I_Big) = Psi ** (2 * (2 * I_Big * (J_Big + Mid_Big) + I_Big)),
                                        Lemma_Pow_Mult (Psi, To_Big_Integer (2), 2 * I_Big * (J_Big + Mid_Big) + I_Big)
                                    ));
                                    pragma Assert (B_J_Plus_Mid_Very_Inner (I_Dex) = Psi_Square ** (2 * I_Big * (J_Big + Mid_Big) + I_Big) * E_Odd (I_Dex));
                                    pragma Assert (B_J_Plus_Mid_Very_Inner (I_Dex) = Psi ** (2 * (2 * I_Big * (J_Big + Mid_Big) + I_Big)) * E_Odd (I_Dex));
                                    pragma Assert (B_J_Plus_Mid_Very_Inner (I_Dex) = Psi ** (2 * (2 * I_Big) * (J_Big + Mid_Big) + (2 * I_Big)) * E_Odd (I_Dex));
                                    pragma Assert (B_J_Plus_Mid_Very_Inner (I_Dex) = Psi ** ((2 * (2 * I_Big) * J_Big + (2 * I_Big)) + 4 * I_Big * Mid_Big) * E_Odd (I_Dex));
                                    pragma Assert (By (
                                        B_J_Plus_Mid_Very_Inner (I_Dex) = (Psi ** (2 * (2 * I_Big) * J_Big + (2 * I_Big)) * Psi ** (4 * I_Big * Mid_Big)) * E_Odd (I_Dex), 
                                        Lemma_Pow_Additive (Psi, 2 * (2 * I_Big) * J_Big + (2 * I_Big), 4 * I_Big * Mid_Big)
                                    ));
                                    pragma Assert (By (
                                        Psi ** (4 * I_Big * Mid_Big) = (Psi ** (4 * Mid_Big)) ** I_Big,
                                        Lemma_Pow_Mult (Psi, 4 * Mid_Big, I_Big)
                                    ));
                                pragma Assert (B_J_Plus_Mid_Very_Inner (I_Dex) = B_J_Very_Inner (I_Dex));

                                pragma Assert (B_Bis_Minus_Very_Inner (I_Dex) = (- Psi ** (2 * J_Big + 1)) * B_J_Plus_Mid_Very_Inner (I_Dex));
                                    pragma Assert (B_Bis_Minus_Very_Inner (I_Dex) = (- Psi ** (2 * J_Big + 1)) * B_J_Very_Inner (I_Dex));
                                    pragma Assert (By (
                                        B_Bis_Minus_Very_Inner (I_Dex) = ((-1) * Psi ** (2 * J_Big + 1)) * B_J_Very_Inner (I_Dex),
                                        Lemma_Minus_Factor (0, Psi ** (2 * J_Big + 1))
                                    ));
                                    pragma Assert (By (
                                        ((-1) * Psi ** (2 * J_Big + 1)) * B_J_Very_Inner (I_Dex) = (-1) * (Psi ** (2 * J_Big + 1) * B_J_Very_Inner (I_Dex)),
                                        Lemma_Mult_Associative (-1, Psi ** (2 * J_Big + 1), B_J_Very_Inner (I_Dex))
                                    ));
                                    pragma Assert (B_Bis_Minus_Very_Inner (I_Dex) = (-1) * ((Psi ** (2 * J_Big + 1)) * (Psi ** (4 * I_Big * J_Big + 2 * I_Big) * E_Odd (I_Dex))));
                                    pragma Assert (By (
                                        Psi ** (2 * I_Big * To_Big_Integer (E'Length)) = (Psi ** (2 * To_Big_Integer (E'Length))) ** I_Big,
                                        Lemma_Pow_Mult (Psi, 2 * To_Big_Integer (E'Length), I_Big)
                                    ));
                                    pragma Assert (By (
                                        Psi ** (2 * To_Big_Integer (E'Length)) = (Psi ** To_Big_Integer (E'Length)) ** To_Big_Integer (2),
                                        Lemma_Pow_Mult (Psi, To_Big_Integer (2), To_Big_Integer (E'Length))
                                    ));
                                    pragma Assert (1 ** (I_Big) = 1);
                                    pragma Assert (Psi ** (2 * I_Big * To_Big_Integer (E'Length)) = ((Psi ** To_Big_Integer (E'Length)) ** To_Big_Integer (2)) ** I_Big);
                                    pragma Assert (B_Bis_Minus_Very_Inner (I_Dex) = (Psi ** To_Big_Integer (E'Length)) * ((Psi ** (2 * J_Big + 1)) * (Psi ** (4 * I_Big * J_Big + 2 * I_Big))) * E_Odd (I_Dex));
                                    pragma Assert (By (
                                        (Psi ** (2 * J_Big + 1)) * (Psi ** (4 * I_Big * J_Big + 2 * I_Big)) =  Psi ** (4 * I_Big * J_Big + 2 * I_Big + 2 * J_Big + 1),
                                        Lemma_Pow_Additive (Psi, 2 * J_Big + 1, 4 * I_Big * J_Big + 2 * I_Big)
                                    ));
                                    pragma Assert (B_Bis_Minus_Very_Inner (I_Dex) = (Psi ** To_Big_Integer (E'Length)) * (Psi ** (4 * I_Big * J_Big + 2 * I_Big + 2 * J_Big + 1) * E_Odd (I_Dex)));
                                    pragma Assert (B_Bis_Minus_Very_Inner (I_Dex) = (Psi ** To_Big_Integer (E'Length)) * ((Psi ** (2 * I_Big * To_Big_Integer (E'Length))) * Psi ** (4 * I_Big * J_Big + 2 * I_Big + 2 * J_Big + 1) * E_Odd (I_Dex)));
                                    pragma Assert (2 * Mid_Big = To_Big_Integer (E'Length));
                                    pragma Assert (By (
                                        (Psi ** To_Big_Integer (E'Length)) * (Psi ** (2 * I_Big * To_Big_Integer (E'Length))) = Psi ** (To_Big_Integer (E'Length) + 2 * I_Big * To_Big_Integer (E'Length)),
                                        Lemma_Pow_Additive (Psi, To_Big_Integer (E'Length), 2 * I_Big * To_Big_Integer (E'Length))
                                    ));
                                    pragma Assert (By (
                                        Psi ** (To_Big_Integer (E'Length) + 2 * I_Big * To_Big_Integer (E'Length)) * Psi ** (4 * I_Big * J_Big + 2 * I_Big + 2 * J_Big + 1) = Psi ** (To_Big_Integer (E'Length) + 2 * I_Big * To_Big_Integer (E'Length) + 4 * I_Big * J_Big + 2 * I_Big + 2 * J_Big + 1),
                                        Lemma_Pow_Additive (Psi, To_Big_Integer (E'Length) + 2 * I_Big * To_Big_Integer (E'Length), 4 * I_Big * J_Big + 2 * I_Big)
                                    ));
                                    pragma Assert (B_Bis_Minus_Very_Inner (I_Dex) = Psi ** (To_Big_Integer (E'Length) + 2 * I_Big * To_Big_Integer (E'Length) + 4 * I_Big * J_Big + 2 * I_Big + 2 * J_Big + 1) * E_Odd (I_Dex));
                                    pragma Assert (B_Bis_Minus_Very_Inner (I_Dex) = Psi ** (2 * (2 * I_Big + 1) * (J_Big + Mid_Big) + (2 * I_Big + 1)) * E (2 * I_Dex + 1));
                                    pragma Assert (B_Bis_Minus_Very_Inner (I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex + Mid_Dex, 2 * I_Dex + 1));
                                pragma Assert (B_Bis_Minus_Very_Inner (I_Dex) = Big_Array_Plus_Mid (2 * I_Dex + 1));
                            end;
                        end loop;
                        -- For J
                            pragma Assert (A_J_Very_Inner = Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex));
                            pragma Assert (By (
                                A_Ref (J_Dex) = Generic_Sum.Sum (A_J_Very_Inner),
                                Generic_Sum.Lemma_Sum_Extensional (A_J_Very_Inner, Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex))
                            ));
                            pragma Assert (A_Recurs (J_Dex) = Generic_Sum.Sum (A_J_Very_Inner));

                            -- Same for B
                            pragma Assert (B_J_Very_Inner = Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex));
                            pragma Assert (By (
                                B_Ref (J_Dex) = Generic_Sum.Sum (B_J_Very_Inner),
                                Generic_Sum.Lemma_Sum_Extensional (B_J_Very_Inner, Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex))
                            ));
                            pragma Assert (B_Recurs (J_Dex) = Generic_Sum.Sum (B_J_Very_Inner));
    
                            B_Bis (J_Dex) := Generic_Sum.Sum (B_Bis_Very_Inner);

                            pragma Assert (By (
                                Generic_Sum.Sum (Generic_Sum.Scalar_Mult (Psi ** (2 * J_Big + 1), B_J_Very_Inner)) = ((Psi ** (2 * J_Big + 1)) *  Generic_Sum.Sum (B_J_Very_Inner)),
                                Generic_Sum.Lemma_Sum_Linear_Scal_Mult (Psi ** (2 * J_Big + 1), B_J_Very_Inner)
                            ));
                            pragma Assert (Generic_Sum.Scalar_Mult (Psi ** (2 * J_Big + 1), B_J_Very_Inner) = B_Bis_Very_Inner);
                            pragma Assert (By (
                                Generic_Sum.Sum (Generic_Sum.Scalar_Mult (Psi ** (2 * J_Big + 1), B_J_Very_Inner)) = Generic_Sum.Sum (B_Bis_Very_Inner), 
                                Generic_Sum.Lemma_Sum_Extensional (Generic_Sum.Scalar_Mult (Psi ** (2 * J_Big + 1), B_J_Very_Inner), B_Bis_Very_Inner)
                            ));
                            pragma Assert (Generic_Sum.Sum (B_Bis_Very_Inner) = (Psi ** (2 * J_Big + 1)) * Generic_Sum.Sum (B_J_Very_Inner));
                            pragma Assert (B_Bis (J_Dex) = (Psi ** (2 * J_Big + 1)) * B_Recurs (J_Dex));

                        Res (J_Dex) := A_Recurs (J_Dex) + (Psi ** (2 * J_Big + 1)) * B_Recurs (J_Dex);

                            pragma Assert (Res (J_Dex) = A_Recurs (J_Dex) + (Psi ** (2 * J_Big + 1)) * B_Recurs (J_Dex));
                            pragma Assert (Res (J_Dex) = A_Recurs (J_Dex) + B_Bis (J_Dex));
                        -- The sum being on the even and odd terms
                        pragma Assert (Res (J_Dex) = Generic_Sum.Sum (Big_Array));
                            pragma Assert (Res (J_Dex) = NTT_Inner_Ref (E, Psi, 0, J_Dex));
                            pragma Assert (Res (J_Dex) = Array_Generator_Inner (E, Psi, 0) (J_Dex));
                            pragma Assert (Goal (J_Dex) = Array_Generator_Inner (E, Psi, 0) (J_Dex));
                        pragma Assert (Res (J_Dex) = Goal (J_Dex));

                        -- Now for J+Mid_Dex

                        Res (J_Dex + Mid_Dex) := A_Recurs (J_Dex) - Psi ** (2 * J_Big + 1) * B_Recurs (J_Dex);

                        pragma Assert (Res (J_Dex + Mid_Dex) = A_Recurs (J_Dex) - B_Bis (J_Dex));

                        pragma Assert (Res (J_Dex + Mid_Dex) = A_Recurs (J_Dex) - Psi ** (2 * J_Big + 1) * B_Recurs (J_Dex));

                        pragma Assert (By (
                            A_Recurs (J_Dex) - Psi ** (2 * J_Big + 1) * B_Recurs (J_Dex) = A_Recurs (J_Dex) + (-1) * (Psi ** (2 * J_Big + 1) * B_Recurs (J_Dex)),
                            Lemma_Minus_Factor (A_Recurs (J_Dex), Psi ** (2 * J_Big + 1) * B_Recurs (J_Dex))
                        ));
                        pragma Assert (By (
                            ((-1) * (Psi ** (2 * J_Big + 1))) * B_Recurs (J_Dex) = (-1) * (Psi ** (2 * J_Big + 1) * B_Recurs (J_Dex)), 
                            Lemma_Mult_Associative (-1, Psi ** (2 * J_Big + 1), B_Recurs (J_Dex))
                        ));
                        pragma Assert (Res (J_Dex + Mid_Dex) = A_Recurs (J_Dex) + ((-1) * (Psi ** (2 * J_Big + 1))) * B_Recurs (J_Dex));
                        pragma Assert (Res (J_Dex + Mid_Dex) = A_Recurs (J_Dex) + ((Psi ** To_Big_Integer (E'Length)) * (Psi ** (2 * J_Big + 1))) * B_Recurs (J_Dex));
                        pragma Assert (By (
                            Res (J_Dex + Mid_Dex) = A_Recurs (J_Dex) + (Psi ** (To_Big_Integer (E'Length) + 2 * J_Big + 1) * B_Recurs (J_Dex)), 
                            Lemma_Pow_Additive (Psi, To_Big_Integer (E'Length), 2 * To_Big (J_Dex) + 1)
                        ));

                        pragma Assert (To_Big_Integer (E'Length) + 2 * J_Big + 1 = 2 * (To_Big_Integer (E'Length) / 2 + J_Big) + 1);

                        pragma Assert (Res (J_Dex + Mid_Dex) = A_Recurs (J_Dex) + (Psi ** (2 * (To_Big_Integer (E'Length) / 2 + J_Big) + 1) * B_Recurs (J_Dex)));
                        pragma Assert (To_Big_Integer (E'Length) / 2 + J_Big = To_Big (J_Dex + Mid_Dex));
                        pragma Assert (Res (J_Dex + Mid_Dex) = A_Recurs (J_Dex) + (Psi ** (2 * To_Big (J_Dex + Mid_Dex) + 1) * B_Recurs (J_Dex)));


                        --  Plus qu'à montrer que A_Recurs (J_Dex) = A_Ref (J_Dex) = \sum n/2 |

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
                pragma Assert (Res = Goal);
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
                                 A : Big_Integer;
                                 B : Big_Integer) return Boolean
    is 
    begin
        pragma Assume (X ** (A + B) = (X ** A) * (X ** B));
        return True;
    end Lemma_Pow_Additive;

    function Lemma_Pow_Mult (X : T_ref;
                             A : Big_Integer;
                             B : Big_Integer) return Boolean
    is
    begin
        pragma Assume ((X ** A) ** B = X ** (A * B));
        return True;
    end Lemma_Pow_Mult;


end RecursNTT;