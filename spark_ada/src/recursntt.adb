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
    begin
        if E'Length = 1 then
            Res (0) := E (0);
        else
            declare
                Is_Pow_Of_Two_Def : constant Boolean := Lemma_Is_Pow_Of_Two_Def (E'Length);
                E_Even : Array_Zq renames Generic_Sum.Extract_Even (E);
                E_Odd : Array_Zq renames Generic_Sum.Extract_Odd (E);
                Psi_Square : T_Ref renames Square (E, Psi);
                A_Recurs : Array_Zq renames NTT_Recurs (E_Even, Psi_Square);
                B_Recurs : Array_Zq renames NTT_Recurs (E_Odd, Psi_Square);
            begin
                for J_Dex in 0 .. Index_Ref (E'Length / 2) - 1 loop
                        Res (J_Dex) := A_Recurs (J_Dex) + Psi ** (2 * To_Big (J_Dex) + 1) * B_Recurs (J_Dex);
                        Res (J_Dex + Index_Ref (E'Length / 2)) := A_Recurs (J_Dex) + (- Psi ** (2 * To_Big (J_Dex) + 1)) * B_Recurs (J_Dex);
                        declare
                          Small_Val : constant T_Ref := Val_Small (E, Psi, J_Dex) with Ghost;
                          Big_Val   : constant T_Ref := Val_Big (E, Psi, J_Dex + Index_Ref (E'Length / 2)) with Ghost;
                        begin
                          pragma Assert (Res (J_Dex)'Initialized and then
                                Res (J_Dex) = Small_Val);
                          pragma Assert (Res (J_Dex + Index_Ref (E'Length / 2))'Initialized and then
                                Res (J_Dex + Index_Ref (E'Length / 2)) = Big_Val);
                        end;

                        pragma Loop_Invariant (
                            (for all J in 0 .. J_Dex => (
                                Res (J)'Initialized and then
                                Res (J) = Val_Small (E, Psi, J)
                            )) 
                        );
                        pragma Loop_Invariant (
                            (for all J in Index_Ref (E'Length / 2) .. J_Dex + Index_Ref (E'Length / 2) => (
                                Res (J)'Initialized and then
                                Res (J) = Val_Big (E, Psi, J)
                            )) 
                        );
                end loop;
            end;
        end if;
        return Res;
    end NTT_Recurs;

   procedure Lift1 (E_Even, E : Array_Zq; Psi : T_Ref; J_Dex : Index_Ref) with
     Pre => (E'Length > 1 and then Is_Pow_Of_Two (E'Length / 2)) and then
     (Psi ** To_Big_Integer (E'Length) = - 1 and
        (E'First = 0 and E'Last >= E'First and E'Length <= Integer (Index_Ref'Last + 1))) and then  
     (Is_Pow_Of_Two (E'Length)) and then J_Dex in 0 .. Index_Ref (E'Length / 2) - 1
     and then (E_Even'First = 0 and then E_Even'Last = Index_Ref (E'Length / 2) - 1)
     and then (for all I_Dex in E_Even'Range =>
                 (Array_Generator_Very_Inner (E_Even, Square (E, Psi), J_Dex) (I_Dex) = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex)) (I_Dex))),
     Post => NTT_Ref (E_Even, Square (E, Psi)) (J_Dex) = Generic_Sum.Sum (Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex)));

   procedure Lift1 (E_Even, E : Array_Zq; Psi : T_Ref; J_Dex : Index_Ref) is -- For the even terms
      Psi_Square : T_Ref renames Square (E, Psi);
   begin
      begin
         pragma Assert (for all I_Dex in E_Even'Range => 
                          Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex) (I_Dex) = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex)) (I_Dex));
         pragma Assert_And_Cut (Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex) = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex)));
      end;
      pragma Assert (By (
                     Generic_Sum.Sum (Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex)) = Generic_Sum.Sum (Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex))),
                     Generic_Sum.Lemma_Sum_Extensional (Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex) , Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex)))
                    ));
      pragma Assert (NTT_Ref (E_Even, Psi_Square) (J_Dex) = NTT_Inner_Ref (E_Even, Psi_Square, 0, J_Dex));
      pragma Assert (NTT_Ref (E_Even, Psi_Square) (J_Dex) = Generic_Sum.Sum (Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex)));
   end Lift1;

   procedure Lift2 (E_Odd, E : Array_Zq; Psi : T_Ref; J_Dex : Index_Ref) with
     Pre => (E'Length > 1 and then Is_Pow_Of_Two (E'Length / 2)) and then
     (Psi ** To_Big_Integer (E'Length) = - 1 and
        (E'First = 0 and E'Last >= E'First and E'Length <= Integer (Index_Ref'Last + 1))) and then  
     (Is_Pow_Of_Two (E'Length)) and then J_Dex in 0 .. Index_Ref (E'Length / 2) - 1
     and then (E_Odd'First = 0 and then E_Odd'Last = Index_Ref (E'Length / 2) - 1)
     and then (for all I_Dex in E_Odd'Range =>
                 (Psi ** (2 * To_Big (J_Dex) + 1)) * Array_Generator_Very_Inner (E_Odd, Square (E, Psi), J_Dex) (I_Dex) = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex)) (I_Dex)),
     Post => (Psi ** (2 * To_Big (J_Dex) + 1)) * NTT_Ref (E_Odd, Square (E, Psi)) (J_Dex) = Generic_Sum.Sum (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex)));

   procedure Lift2 (E_Odd, E : Array_Zq; Psi : T_Ref; J_Dex : Index_Ref) is -- For the even terms
      Psi_Square : T_Ref renames Square (E, Psi);
   begin
      begin -- One one side Sum of Generic_Sum.Scalar_Mult (- Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)) equals ... 
         begin
            pragma Assert (Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)'First = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex))'First);
            pragma Assert (Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)'Length = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex))'Length);
            pragma Assert (for all I_Dex in E_Odd'Range => (
                                                            (Psi ** (2 * To_Big (J_Dex) + 1)) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I_Dex) = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex)) (I_Dex)
                                                           ));
            pragma Assert_And_Cut (for all I_Dex in E_Odd'Range => (Psi ** (2 * To_Big (J_Dex) + 1)) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I_Dex) = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex)) (I_Dex));
         end;
         pragma Assert (By (
                        Generic_Sum.Sum (Generic_Sum.Scalar_Mult (Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex))) = Generic_Sum.Sum (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex))),
                        Generic_Sum.Lemma_Sum_Extensional (Generic_Sum.Scalar_Mult (Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)), Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex)))
                       ));
         pragma Assert_And_Cut (Generic_Sum.Sum (Generic_Sum.Scalar_Mult (Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex))) = Generic_Sum.Sum (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex))));
      end;
      begin -- One the other side Sum of Generic_Sum.Scalar_Mult (Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)) equals ... , 
         pragma Assert (NTT_Ref (E_Odd, Psi_Square) (J_Dex) = NTT_Inner_Ref (E_Odd, Psi_Square, 0, J_Dex));
         begin
            pragma Assert (for all I_Dex in E_Odd'Range => (Generic_Sum.Scalar_Mult (Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)) (I_Dex) = (Psi ** (2 * To_Big (J_Dex) + 1)) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I_Dex)));
            pragma Assert (By (
                                   Generic_Sum.Sum (Generic_Sum.Scalar_Mult (Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex))) = (Psi ** (2 * To_Big (J_Dex) + 1)) * Generic_Sum.Sum (Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)),
                                   Generic_Sum.Lemma_Sum_Linear_Scal_Mult (Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex), Generic_Sum.Scalar_Mult (Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)))
                                  ));
           pragma Assert_And_Cut (Generic_Sum.Sum (Generic_Sum.Scalar_Mult (Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex))) = (Psi ** (2 * To_Big (J_Dex) + 1)) * Generic_Sum.Sum (Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex))
                                   );
         end;
         pragma Assert (Generic_Sum.Sum (Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)) = NTT_Ref (E_Odd, Psi_Square) (J_Dex));
         pragma Assert (Generic_Sum.Sum (Generic_Sum.Scalar_Mult (Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex))) = (Psi ** (2 * To_Big (J_Dex) + 1)) * NTT_Ref (E_Odd, Psi_Square) (J_Dex));
      end;
   end Lift2;

   procedure Lift3 (E_Even, E : Array_Zq; Psi : T_Ref; J_Dex : Index_Ref) with
     Pre => (E'Length > 1 and then Is_Pow_Of_Two (E'Length / 2)) and then
     (Psi ** To_Big_Integer (E'Length) = - 1 and
        (E'First = 0 and E'Last >= E'First and E'Length <= Integer (Index_Ref'Last + 1))) and then  
     (Is_Pow_Of_Two (E'Length)) and then J_Dex in 0 .. Index_Ref (E'Length / 2) - 1
     and then (E_Even'First = 0 and then E_Even'Last = Index_Ref (E'Length / 2) - 1)
     and then (for all I_Dex in E_Even'Range =>
                 (Array_Generator_Very_Inner (E_Even, Square (E, Psi), J_Dex) (I_Dex) = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex + Index_Ref (E'Length / 2))) (I_Dex))),
     Post => NTT_Ref (E_Even, Square (E, Psi)) (J_Dex) = Generic_Sum.Sum (Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex + Index_Ref (E'Length / 2))));

   procedure Lift3 (E_Even, E : Array_Zq; Psi : T_Ref; J_Dex : Index_Ref) is -- For the even terms
      Psi_Square : T_Ref renames Square (E, Psi);
      Mid_Dex    : Index_Ref := Index_Ref (E'Length / 2); 
   begin
      begin
         pragma Assert (for all I_Dex in E_Even'Range => 
                          Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex) (I_Dex) = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)) (I_Dex));
         pragma Assert_And_Cut (Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex) = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)));
      end;
      pragma Assert (By (
                     Generic_Sum.Sum (Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex)) = Generic_Sum.Sum (Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex))),
                     Generic_Sum.Lemma_Sum_Extensional (Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex) , Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)))
                    ));
      pragma Assert (NTT_Ref (E_Even, Psi_Square) (J_Dex) = NTT_Inner_Ref (E_Even, Psi_Square, 0, J_Dex));
      pragma Assert (NTT_Ref (E_Even, Psi_Square) (J_Dex) = Generic_Sum.Sum (Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex)));
   end Lift3;

   procedure Lift4 (E_Odd, E : Array_Zq; Psi : T_Ref; J_Dex : Index_Ref) with
     Pre => (E'Length > 1 and then Is_Pow_Of_Two (E'Length / 2)) and then
     (Psi ** To_Big_Integer (E'Length) = - 1 and
        (E'First = 0 and E'Last >= E'First and E'Length <= Integer (Index_Ref'Last + 1))) and then  
     (Is_Pow_Of_Two (E'Length)) and then J_Dex in 0 .. Index_Ref (E'Length / 2) - 1
     and then (E_Odd'First = 0 and then E_Odd'Last = Index_Ref (E'Length / 2) - 1)
     and then (for all I_Dex in E_Odd'Range =>
                 (- Psi ** (2 * To_Big (J_Dex) + 1)) * Array_Generator_Very_Inner (E_Odd, Square (E, Psi), J_Dex) (I_Dex) = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Index_Ref (E'Length / 2))) (I_Dex)),
     Post => (- Psi ** (2 * To_Big (J_Dex) + 1)) * NTT_Ref (E_Odd, Square (E, Psi)) (J_Dex) = Generic_Sum.Sum (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Index_Ref (E'Length / 2))));

   procedure Lift4 (E_Odd, E : Array_Zq; Psi : T_Ref; J_Dex : Index_Ref) is -- For the even terms
      Psi_Square : T_Ref renames Square (E, Psi);
      Mid_Dex    : Index_Ref := Index_Ref (E'Length / 2); 
   begin
      begin -- One one side Sum of Generic_Sum.Scalar_Mult (- Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)) equals ... 
         begin
            pragma Assert (Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)'First = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex))'First);
            pragma Assert (Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)'Length = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex))'Length);
            pragma Assert (for all I_Dex in E_Odd'Range => (
                                                            (- Psi ** (2 * To_Big (J_Dex) + 1)) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I_Dex) = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)) (I_Dex)
                                                           ));
            pragma Assert_And_Cut (for all I_Dex in E_Odd'Range => (- Psi ** (2 * To_Big (J_Dex) + 1)) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I_Dex) = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)) (I_Dex));
         end;
         pragma Assert (By (
                        Generic_Sum.Sum (Generic_Sum.Scalar_Mult (- Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex))) = Generic_Sum.Sum (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex))),
                        Generic_Sum.Lemma_Sum_Extensional (Generic_Sum.Scalar_Mult (- Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)), Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)))
                       ));
         pragma Assert_And_Cut (Generic_Sum.Sum (Generic_Sum.Scalar_Mult (- Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex))) = Generic_Sum.Sum (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex))));
      end;
      begin -- One the other side Sum of Generic_Sum.Scalar_Mult (- Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)) equals ... , 
         pragma Assert (NTT_Ref (E_Odd, Psi_Square) (J_Dex) = NTT_Inner_Ref (E_Odd, Psi_Square, 0, J_Dex));
         begin
            pragma Assert (for all I_Dex in E_Odd'Range => (Generic_Sum.Scalar_Mult (- Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)) (I_Dex) = (- Psi ** (2 * To_Big (J_Dex) + 1)) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I_Dex)));
            pragma Assert (By (
                                   Generic_Sum.Sum (Generic_Sum.Scalar_Mult (- Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex))) = (- Psi ** (2 * To_Big (J_Dex) + 1)) * Generic_Sum.Sum (Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)),
                                   Generic_Sum.Lemma_Sum_Linear_Scal_Mult (- Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex), Generic_Sum.Scalar_Mult (- Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)))
                                  ));
           pragma Assert_And_Cut (Generic_Sum.Sum (Generic_Sum.Scalar_Mult (- Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex))) = (- Psi ** (2 * To_Big (J_Dex) + 1)) * Generic_Sum.Sum (Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex))
                                   );
         end;
         pragma Assert (Generic_Sum.Sum (Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)) = NTT_Ref (E_Odd, Psi_Square) (J_Dex));
         pragma Assert (Generic_Sum.Sum (Generic_Sum.Scalar_Mult (- Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex))) = (- Psi ** (2 * To_Big (J_Dex) + 1)) * NTT_Ref (E_Odd, Psi_Square) (J_Dex));
      end;
   end Lift4;

    function Lemma_Recurs_Equiv_Ref (E : Array_Zq ; Psi : T_Ref) return Boolean
    is
    begin
        if E'Length = 1 then
            pragma Assert (Array_Generator_Very_Inner (E, Psi, 0) (0) = E (0));
            pragma Assert (Generic_Sum.Sum (Array_Generator_Very_Inner (E, Psi, 0)) = E (0));
            pragma Assert (NTT_Inner_Ref (E, Psi, 0, 0)  = E (0));
            pragma Assert (NTT_Ref (E, Psi) (0) = E(0));
            pragma Assert (NTT_Recurs (E, Psi) (0) = E (0));
            pragma Assert (NTT_Ref (E, Psi) = NTT_Recurs (E, Psi));
        else
            declare
                Is_Pow_Of_Two_Def : constant Boolean := Lemma_Is_Pow_Of_Two_Def (E'Length);
                E_Even : Array_Zq renames Generic_Sum.Extract_Even (E);
                E_Odd : Array_Zq renames Generic_Sum.Extract_Odd (E);
                Psi_Square : T_Ref renames Square (E, Psi);
                Induction_Hypothesis_Even : Boolean := Lemma_Recurs_Equiv_Ref (E_Even, Psi_Square);
                Induction_Hypothesis_Odd : Boolean := Lemma_Recurs_Equiv_Ref (E_Odd, Psi_Square);

                Mid_Dex : Index_Ref := Index_Ref (E'Length / 2); 
            begin
                begin
                for J_Dex in 0 .. Mid_Dex - 1 loop
                    begin
                    for I_Dex in 0 .. Mid_Dex - 1 loop
                        begin
                            rewrite1 (E, E_Even, Psi, Psi_Square, J_Dex, I_Dex, To_Big (J_Dex), To_Big (I_Dex));
                            pragma Assert (NTT_Very_Inner_Ref (E_Even, Psi_Square, J_Dex, I_Dex) = Array_Generator_Very_Inner (E, Psi, J_Dex) (2 * I_Dex));
                            pragma Assert_And_Cut (Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex) (I_Dex) = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex)) (I_Dex));
                        end;
                        begin
                            rewrite2 (E, E_Odd, Psi, Psi_Square, J_Dex, I_dex, To_Big (J_Dex), To_Big (I_Dex));
                            pragma Assert (Psi ** (2 * To_Big (J_Dex) + 1) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I_Dex) = Array_Generator_Very_Inner (E, Psi, J_Dex) (2 * I_Dex + 1));
                            pragma Assert_And_Cut (Psi ** (2 * To_Big (J_Dex) + 1) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I_Dex) = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex)) (I_Dex));
                        end;

                        pragma Loop_Invariant (for all I in 0 .. I_Dex => (
                            Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex) (I) = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex)) (I) and
                            Psi ** (2 * To_Big (J_Dex) + 1) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I) = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex)) (I)
                        ));
                    end loop;

                        pragma Assert_And_Cut (for all I in 0 .. Mid_Dex - 1 => (
                            Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex) (I) = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex)) (I) and
                            Psi ** (2 * To_Big (J_Dex) + 1) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I) = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex)) (I)
                        ));
                    end;

                    begin -- For J_Dex
                        begin
                            pragma Assert (By (NTT_Recurs (E, Psi) (J_Dex) = NTT_Recurs (Generic_Sum.Extract_Even (E), Square (E, Psi)) (J_Dex) + 
                                             Psi ** (2 * To_Big (J_Dex) + 1) * NTT_Recurs (Generic_Sum.Extract_Odd (E), Square (E, Psi)) (J_Dex),
                                           NTT_Recurs (E, Psi) (J_Dex) = Val_Small (E, Psi, J_Dex)));


                            begin -- For the even terms
                                Lift1 (E_Even, E, Psi, J_Dex);
                                pragma Assert (NTT_Recurs (E_Even, Psi_Square) (J_Dex) = NTT_Ref (E_Even, Psi_Square) (J_Dex));
                                pragma Assert_And_Cut (NTT_Recurs (E_Even, Psi_Square) (J_Dex) = Generic_Sum.Sum (Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex))));
                            end;
                            begin -- For the odd terms
                                Lift2 (E_Odd, E, Psi, J_Dex);
                                pragma Assert (NTT_Recurs (E_Odd, Psi_Square) (J_Dex) = NTT_Ref (E_Odd, Psi_Square) (J_Dex));
                                -- So ...
                                pragma Assert_And_Cut ((Psi ** (2 * To_Big (J_Dex) + 1)) * NTT_Recurs (E_Odd, Psi_Square) (J_Dex) = Generic_Sum.Sum (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex))));
                            end;
                            pragma Assert_And_Cut (
                                NTT_Recurs (E, Psi) (J_Dex) = 
                                    Generic_Sum.Sum (Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex))) + 
                                    Generic_Sum.Sum (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex)))
                            );
                        end;
                        pragma Assert (By (
                            Generic_Sum.Sum (Array_Generator_Very_Inner (E, Psi, J_Dex)) = 
                                    Generic_Sum.Sum (Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex))) +
                                    Generic_Sum.Sum (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex)))
                            ,
                            Generic_Sum.Lemma_Split_Odd_Even (Array_Generator_Very_Inner (E, Psi, J_Dex))
                        ));
                        pragma Assert
                         (By (NTT_Ref (E, Psi) (J_Dex) = Generic_Sum.Sum (Array_Generator_Very_Inner (E, Psi, J_Dex)),
                              NTT_Ref (E, Psi) (J_Dex) = NTT_Inner_Ref (E, Psi, 0, J_Dex)));
                        pragma Assert_And_Cut (NTT_Ref (E, Psi) (J_Dex) = NTT_Recurs (E, Psi) (J_Dex));
                    end;
                    pragma Loop_Invariant (for all I_Dex in 0 .. J_Dex => (
                        NTT_Recurs (E, Psi) (I_Dex) = NTT_Ref (E, Psi) (I_Dex)
                    ));
                end loop;
                    pragma Assert_And_Cut (for all J_Dex in 0 .. Mid_Dex - 1 => (
                        NTT_Recurs (E, Psi) (J_Dex) = NTT_Ref (E, Psi) (J_Dex)
                    ));
            end;
                begin
                for J_Dex in 0 .. Mid_Dex - 1 loop
                    begin
                    for I_Dex in 0 .. Mid_Dex - 1 loop
                        begin
                            rewrite3 (E, E_Even, Psi, Psi_Square, Mid_Dex, J_Dex, I_Dex, To_Big (Mid_Dex), To_Big (J_Dex), To_Big (I_Dex));
                            pragma Assert (NTT_Very_Inner_Ref (E_Even, Psi_Square, J_Dex, I_Dex) = Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex) (2 * I_Dex));
                            pragma Assert_And_Cut (Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex) (I_Dex) = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)) (I_Dex));
                        end;
                        begin
                            rewrite4 (E, E_Odd, Psi, Psi_Square, Mid_Dex, J_Dex, I_Dex, To_Big (Mid_Dex), To_Big (J_Dex), To_Big (I_Dex));
                            pragma Assert ((- Psi ** (2 * To_Big (J_Dex) + 1)) * NTT_Very_Inner_Ref (E_Odd, Psi_Square, J_Dex, I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex + Mid_Dex, 2 * I_Dex + 1));
                            pragma Assert (By ((- Psi ** (2 * To_Big (J_Dex) + 1)) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I_Dex) = Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex) (2 * I_Dex + 1),
                                           Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I_Dex) = NTT_Very_Inner_Ref (E_Odd, Psi_Square, J_Dex, I_Dex)
                                           and Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex) (2 * I_Dex + 1) = NTT_Very_Inner_Ref (E, Psi, J_Dex + Mid_Dex, 2 * I_Dex + 1)));
                            pragma Assert (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)) (I_Dex) = Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex) (2 * I_Dex + 1));
                            pragma Assert_And_Cut ((- Psi ** (2 * To_Big (J_Dex) + 1)) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I_Dex) = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)) (I_Dex));
                        end;

                        pragma Loop_Invariant (for all I in 0 .. I_Dex => (
                            Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex) (I) = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)) (I) and
                            (- Psi ** (2 * To_Big (J_Dex) + 1)) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I) = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)) (I)
                        ));
                    end loop;

                        pragma Assert_And_Cut (for all I in 0 .. Mid_Dex - 1 => (
                            Array_Generator_Very_Inner (E_Even, Psi_Square, J_Dex) (I) = Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)) (I) and
                            (- Psi ** (2 * To_Big (J_Dex) + 1)) * Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex) (I) = Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)) (I)
                        ));
                    end;


                    -- For J_Dex, just copy paste what is for J_Dex + Mid_Dex, and replace all occurences of J_Dex + Mid_Dex by J_Dex, - Psi by Psi, Generic_Sum.Scalar_Mult (- Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)) by Generic_Sum.Scalar_Mult (Psi ** (2 * To_Big (J_Dex) + 1), Array_Generator_Very_Inner (E_Odd, Psi_Square, J_Dex)).

                    begin -- For J_Dex + Mid_Dex
                        begin
                            pragma Assert (By (NTT_Recurs (E, Psi) (J_Dex + Mid_Dex) = NTT_Recurs (E_Even, Psi_Square) (J_Dex) + (- Psi ** (2 * To_Big (J_Dex) + 1)) * NTT_Recurs (E_Odd, Psi_Square) (J_Dex),
                                           NTT_Recurs (E, Psi) (J_Dex + Mid_Dex) = Val_Big (E, Psi, J_Dex + Mid_Dex)));


                            begin -- For the even terms
                                pragma Assert (NTT_Recurs (E_Even, Psi_Square) (J_Dex) = NTT_Ref (E_Even, Psi_Square) (J_Dex));
                                Lift3 (E_Even, E, Psi, J_Dex);
                                pragma Assert_And_Cut (NTT_Recurs (E_Even, Psi_Square) (J_Dex) = Generic_Sum.Sum (Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex))));
                            end;
                            begin -- For the odd terms
                                pragma Assert (NTT_Recurs (E_Odd, Psi_Square) (J_Dex) = NTT_Ref (E_Odd, Psi_Square) (J_Dex));
                                Lift4 (E_Odd, E, Psi, J_Dex);
                                -- So ...
                                pragma Assert_And_Cut ((- Psi ** (2 * To_Big (J_Dex) + 1)) * NTT_Recurs (E_Odd, Psi_Square) (J_Dex) = Generic_Sum.Sum (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex))));
                            end;
                            pragma Assert_And_Cut (
                                NTT_Recurs (E, Psi) (J_Dex + Mid_Dex) = 
                                    Generic_Sum.Sum (Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex))) + 
                                    Generic_Sum.Sum (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)))
                            );
                        end;
                        pragma Assert (By (
                            Generic_Sum.Sum (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)) = 
                                    Generic_Sum.Sum (Generic_Sum.Extract_Even (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex))) +
                                    Generic_Sum.Sum (Generic_Sum.Extract_Odd (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)))
                            ,
                            Generic_Sum.Lemma_Split_Odd_Even (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex))
                        ));
                        pragma Assert
                         (By (NTT_Ref (E, Psi) (J_Dex + Mid_Dex) = Generic_Sum.Sum (Array_Generator_Very_Inner (E, Psi, J_Dex + Mid_Dex)),
                              NTT_Ref (E, Psi) (J_Dex + Mid_Dex) = NTT_Inner_Ref (E, Psi, 0, J_Dex + Mid_Dex)));
                        pragma Assert_And_Cut (NTT_Ref (E, Psi) (J_Dex + Mid_Dex) = NTT_Recurs (E, Psi) (J_Dex + Mid_Dex));
                    end;
                    pragma Loop_Invariant (for all I_Dex in Mid_Dex .. J_Dex + Mid_Dex => 
                        NTT_Recurs (E, Psi) (I_Dex) = NTT_Ref (E, Psi) (I_Dex)
                    );
                end loop;
                    pragma Assert_And_Cut (for all J_Dex in Mid_Dex .. E'Length - 1 => (
                        NTT_Recurs (E, Psi) (J_Dex) = NTT_Ref (E, Psi) (J_Dex)
                    ));
            end;
                pragma Assert (NTT_Recurs (E, Psi) = NTT_Ref (E, Psi));
            end;
        end if;
        return True;
    end Lemma_Recurs_Equiv_Ref;

    procedure rewrite1 (E : Array_Zq; E_Even : Array_Zq; Psi : T_Ref; Psi_Square : T_Ref; J_Dex : Index_Ref; I_Dex : Index_Ref; J_Big : Big_Integer ; I_Big : Big_Integer)
    is
        Objective : T_Ref := NTT_Very_Inner_Ref (E_Even, Psi_Square, J_Dex, I_Dex);
    begin
        null;
        pragma Assert (By(
            (Psi ** To_Big_Integer (2)) ** (2 * I_Big * J_Big + I_Big) = Psi ** (2 * (2 * I_Big * J_Big + I_Big)), 
            Lemma_Pow_Mult (Psi, To_Big_Integer (2), 2 * I_Big * J_Big + I_Big)
        ));
        pragma Assert (Objective = Psi_Square ** (2 * I_Big * J_Big + I_Big) * E_Even (I_Dex));
        pragma Assert (Objective = Psi ** (2 * (2 * I_Big * J_Big + I_Big)) * E_Even (I_Dex));
        pragma Assert (Objective = Psi ** (2 * (2 * I_Big) * J_Big + (2 * I_Big)) * E (2 * I_Dex));
        pragma Assert (Psi ** (2 * (2 * I_Big) * J_Big + (2 * I_Big)) * E (2 * I_Dex) = NTT_Very_Inner_Ref (E, Psi, J_Dex, 2 * I_Dex));
        pragma Assert (Objective = NTT_Very_Inner_Ref (E, Psi, J_Dex, 2 * I_Dex));
    end rewrite1;
    
    procedure rewrite2 (E : Array_Zq; E_Odd : Array_Zq; Psi : T_Ref; Psi_Square : T_Ref; J_Dex : Index_Ref; I_Dex : Index_Ref; J_Big : Big_Integer ; I_Big : Big_Integer)
    is
        Objective : T_Ref := Psi ** (2 * J_Big + 1) * NTT_Very_Inner_Ref (E_Odd, Psi_Square, J_Dex, I_Dex);
    begin
        begin
            pragma Assert (By(
                (Psi ** To_Big_Integer (2)) ** (2 * I_Big * J_Big + I_Big) = Psi ** (2 * (2 * I_Big * J_Big + I_Big)), 
                Lemma_Pow_Mult (Psi, To_Big_Integer (2), 2 * I_Big * J_Big + I_Big)
            ));
            pragma Assert (Objective  = (Psi ** (2 * J_Big + 1)) * (Psi ** (4 * I_Big * J_Big + 2 * I_Big) * E_Odd (I_Dex)));
            pragma Assert (By (
                (Psi ** (2 * J_Big + 1) * (Psi ** (4 * I_Big * J_Big + 2 * I_Big)) * E_Odd (I_Dex) = (Psi ** (2 * J_Big + 1)) * (Psi ** (4 * I_Big * J_Big + 2 * I_Big) * E_Odd (I_Dex))),
                Lemma_Mult_Associative (Psi ** (2 * J_Big + 1), (Psi ** (4 * I_Big * J_Big + 2 * I_Big)), E_Odd (I_Dex))
            ));
            pragma Assert (By(
                (Psi ** (2 * J_Big + 1)) * (Psi ** (4 * I_Big * J_Big + 2 * I_Big)) = Psi ** (2 * J_Big + 1 + 4 * I_Big  * J_Big + 2 * I_Big), 
                Lemma_Pow_Additive (Psi, 2 * J_Big + 1, 4 * I_Big * J_Big + 2 * I_Big)
            ));
            pragma Assert (Objective  = Psi ** (4 * I_Big * J_Big + 2 * I_Big + 2 * J_Big + 1) * E_Odd (I_Dex));
            pragma Assert (Objective  = Psi ** (2 * (2 * I_Big + 1) * J_Big + (2 * I_Big + 1)) * E (2 * I_Dex + 1));
            pragma Assert (By (To_Big (2 * I_Dex) = 2 * To_Big (I_Dex), Lemma_Index_Ref_Big_Integer_Additive (I_Dex, I_Dex)));
            pragma Assert (To_Big (2 * I_Dex + 1) = 2 * I_Big + 1);
            pragma Assert_And_Cut (Objective  = Psi ** (2 * (To_Big (2 * I_Dex + 1)) * J_Big + To_Big (2 * I_Dex + 1)) * E (2 * I_Dex + 1));
        end;
        pragma Assert (Objective  = NTT_Very_Inner_Ref (E, Psi, J_Dex, 2 * I_Dex + 1));
    end rewrite2;
    
    procedure rewrite3 (E : Array_Zq; E_Even : Array_Zq; Psi : T_Ref; Psi_Square : T_Ref; Mid_Dex : Index_Ref ; J_Dex : Index_Ref; I_Dex : Index_Ref; Mid_Big : Big_Integer ; J_Big : Big_Integer ; I_Big : Big_Integer)
    is
        Objective : T_Ref := NTT_Very_Inner_Ref (E_Even, Psi_Square, J_Dex, I_Dex);
    begin
        begin
            pragma Assert (Objective = Psi_Square ** (2 * I_Big * J_Big + I_Big) * E_Even (I_Dex));
            begin
                pragma Assert (By (
                    (Psi ** To_Big_Integer (2)) ** (2 * I_Big * (J_Big) + I_Big) = Psi ** (2 * (2 * I_Big * (J_Big) + I_Big)),
                    Lemma_Pow_Mult (Psi, To_Big_Integer (2), 2 * I_Big * (J_Big) + I_Big)
                ));
                pragma Assert_And_Cut (Objective = Psi ** (2 * (2 * I_Big * J_Big + I_Big)) * E_Even (I_Dex));
            end;
            begin
                pragma Assert (By (
                    Psi ** (2 * I_Big * To_Big_Integer (E'Length)) = (Psi ** (2 * To_Big_Integer (E'Length))) ** I_Big,
                    Lemma_Pow_Mult (Psi, 2 * To_Big_Integer (E'Length), I_Big)
                ));
                pragma Assert (By (
                    Psi ** (2 * To_Big_Integer (E'Length)) = (Psi ** To_Big_Integer (E'Length)) ** To_Big_Integer (2),
                    Lemma_Pow_Mult (Psi, To_Big_Integer (E'Length), To_Big_Integer (2))
                ));
                pragma Assert (Psi ** (2 * To_Big_Integer (E'Length) * I_Big) = 1 ** I_Big);
                pragma Assert (By (1**(I_Big) = 1, Lemma_One_Pow_Absorb (I_Big)));
                pragma Assert (Psi ** (2 * I_Big * To_Big_Integer (E'Length)) = 1);
                pragma Assert (By (1 * Psi ** (2 * (2 * I_Big * J_Big + I_Big)) = Psi ** (2 * (2 * I_Big * J_Big + I_Big)), Lemma_One_Mult_Neutral (Psi ** (2 * (2 * I_Big * J_Big + I_Big)))));
                pragma Assert_And_Cut (Psi ** (2 * I_Big * To_Big_Integer (E'Length)) * Psi ** (2 * (2 * I_Big * J_Big + I_Big)) = Psi ** (2 * (2 * I_Big * J_Big + I_Big)));
            end;
            pragma Assert (Objective = Psi ** (2 * I_Big * To_Big_Integer (E'Length)) * Psi ** (2 * (2 * I_Big * J_Big + I_Big)) * E_Even (I_Dex));

            pragma Assert (By (
                Psi ** (2 * (2 * I_Big * J_Big + I_Big) + 2 * I_Big * To_Big_Integer (E'Length)) = Psi ** (2 * I_Big * To_Big_Integer (E'Length)) * Psi ** (2 * (2 * I_Big * J_Big + I_Big)),
                Lemma_Pow_Additive (Psi, 2 * I_Big * To_Big_Integer (E'Length), 2 * (2 * I_Big * J_Big + I_Big))
            ));
            pragma Assert (Objective = Psi ** (2 * (2 * I_Big * J_Big + I_Big) + 4 * I_Big * To_Big_Integer (E'Length) / 2) * E_Even (I_Dex));
            pragma Assert (Objective = Psi ** (2 * (2 * I_Big) * (J_Big + Mid_Big) + (2 * I_Big)) * E (2 * I_Dex));
            pragma Assert (By (J_Big + Mid_Big = To_Big (J_Dex + Mid_Dex), Lemma_Index_Ref_Big_Integer_Additive (Mid_Dex, J_Dex)));
            pragma Assert (To_Big (2 * I_Dex) = 2 * I_Big);
            pragma Assert_And_Cut (Objective = Psi ** (2 * To_Big (2 * I_Dex) * To_Big (J_Dex + Mid_Dex) + To_Big (2 * I_Dex)) * E (2 * I_Dex));
        end;
        pragma Assert (Objective = NTT_Very_Inner_Ref (E, Psi, J_Dex + Mid_Dex, 2 * I_Dex));
    end rewrite3;

    procedure rewrite4 (E : Array_Zq; E_Odd : Array_Zq; Psi : T_Ref; Psi_Square : T_Ref; Mid_Dex : Index_Ref ; J_Dex : Index_Ref; I_Dex : Index_Ref; Mid_Big : Big_Integer ; J_Big : Big_Integer ; I_Big : Big_Integer)

    is

        Objective : T_Ref := (- Psi ** (2 * J_Big + 1)) * NTT_Very_Inner_Ref (E_Odd, Psi_Square, J_Dex, I_Dex);
    begin
        begin
            pragma Assert (Objective = (- Psi ** (2 * J_Big + 1)) * (Psi_Square ** (2 * I_Big * J_Big + I_Big) * E_Odd (I_Dex)));
            begin
                pragma Assert (By (
                    - Psi ** (2 * J_Big + 1) = Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length)), 
                    Lemma_Pow_Additive (Psi, To_Big_Integer (E'Length), 2 * J_Big + 1)
                ));
                pragma Assert (By(
                    (Psi ** To_Big_Integer (2)) ** (2 * I_Big * J_Big + I_Big) = Psi ** (2 * (2 * I_Big * J_Big + I_Big)), 
                    Lemma_Pow_Mult (Psi, To_Big_Integer (2), 2 * I_Big * J_Big + I_Big)
                ));
                pragma Assert_And_Cut (Objective  = Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length)) * (Psi ** (4 * I_Big * J_Big + 2 * I_Big) * E_Odd (I_Dex)));
            end;
            begin
                pragma Assert (By (
                    (Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length)) * Psi ** (4 * I_Big * J_Big + 2 * I_Big)) * E_Odd (I_Dex) = Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length)) * (Psi ** (4 * I_Big * J_Big + 2 * I_Big) * E_Odd (I_Dex)),
                    Lemma_Mult_Associative (Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length)), Psi ** (4 * I_Big * J_Big + 2 * I_Big), E_Odd (I_Dex))
                ));
                pragma Assert (By(
                    Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length)) * Psi ** (4 * I_Big * J_Big + 2 * I_Big) = Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length) + 4 * I_Big * J_Big + 2 * I_Big),
                    Lemma_Pow_Additive (Psi, 2 * J_Big + 1 + To_Big_Integer (E'Length), 4 * I_Big * J_Big + 2 * I_Big)
                ));
                pragma Assert_And_Cut (Objective = Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length) + 4 * I_Big * J_Big + 2 * I_Big) * E_Odd (I_Dex));
            end;
            begin
                pragma Assert (By (
                    Psi ** (2 * I_Big * To_Big_Integer (E'Length)) = (Psi ** (2 * To_Big_Integer (E'Length))) ** I_Big,
                    Lemma_Pow_Mult (Psi, 2 * To_Big_Integer (E'Length), I_Big)
                ));
                pragma Assert (By (
                    Psi ** (2 * To_Big_Integer (E'Length)) = (Psi ** To_Big_Integer (E'Length)) ** To_Big_Integer (2),
                    Lemma_Pow_Mult (Psi, To_Big_Integer (E'Length), To_Big_Integer (2))
                ));
                pragma Assert (Psi ** (2 * To_Big_Integer (E'Length) * I_Big) = 1 ** I_Big);
                pragma Assert (By (1**(I_Big) = 1, Lemma_One_Pow_Absorb (I_Big)));
                pragma Assert (Psi ** (2 * I_Big * To_Big_Integer (E'Length)) = 1);
                pragma Assert (By (
                    Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length) + 4 * I_Big * J_Big + 2 * I_Big) = 
                        Psi ** (2 * I_Big * To_Big_Integer (E'Length)) * 
                        Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length) + 4 * I_Big * J_Big + 2 * I_Big), 
                    Lemma_One_Mult_Neutral (Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length) + 4 * I_Big * J_Big + 2 * I_Big))));
                pragma Assert (By (
                    Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length) + 4 * I_Big * J_Big + 2 * I_Big + 2 * I_Big * To_Big_Integer (E'Length)) = 
                        Psi ** (2 * I_Big * To_Big_Integer (E'Length)) * 
                        Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length) + 4 * I_Big * J_Big + 2 * I_Big),
                    Lemma_Pow_Additive (Psi, 2 * I_Big * To_Big_Integer (E'Length), 2 * J_Big + 1 + To_Big_Integer (E'Length) + 4 * I_Big * J_Big + 2 * I_Big)
                ));
                pragma Assert_And_Cut (Objective = Psi ** (2 * J_Big + 1 + To_Big_Integer (E'Length) + 4 * I_Big * J_Big + 2 * I_Big + 2 * I_Big * To_Big_Integer (E'Length)) * E_Odd (I_Dex));
            end;

            pragma Assert (By (To_Big (2 * I_Dex) = 2 * To_Big (I_Dex), Lemma_Index_Ref_Big_Integer_Additive (I_Dex, I_Dex)));
            pragma Assert (By (To_Big (2 * I_Dex + 1) = 2 * I_Big + 1, Lemma_Index_Ref_Big_Integer_Additive (2  * I_Dex, 1)));
            pragma Assert (By (J_Big + Mid_Big = To_Big (J_Dex + Mid_Dex), Lemma_Index_Ref_Big_Integer_Additive (Mid_Dex, J_Dex)));
            pragma Assert_And_Cut (Objective  = Psi ** (2 * To_Big (2 * I_Dex + 1) * To_Big (J_Dex + Mid_Dex) + To_Big (2 * I_Dex + 1)) * E (2 * I_Dex + 1));
        end;
        pragma Assert (Objective  = NTT_Very_Inner_Ref (E, Psi, J_Dex + Mid_Dex, 2 * I_Dex + 1));
    end rewrite4;

    function Lemma_Index_Ref_Big_Integer_Additive (X : Index_Ref ; Y : Index_Ref) return Boolean
    is
    begin
        pragma Assert (To_Big (X + Y) = To_Big (X) + To_Big (Y));
        return True;
    end Lemma_Index_Ref_Big_Integer_Additive;

    function Lemma_One_Mult_Neutral (X : T_Ref) return Boolean
    is
    begin
        pragma Assert (1 * X = X);
        return True;
    end Lemma_One_Mult_Neutral;

    function Lemma_One_Pow_Absorb (X : Big_Natural) return Boolean
    is
    begin
        if X = 0 then
            pragma Assert (T_Ref (1) ** To_Big_Integer (0) = T_Ref (1));
        else
            declare
                Induction_Hypothesis : Boolean := Lemma_One_Pow_Absorb (X - 1);
            begin
                pragma Assert (T_Ref (1) = T_Ref (1) * T_Ref (1) ** (X - 1));
            end;
        end if;
        pragma Assert (T_Ref (1) ** X = 1);
        return True;
    end Lemma_One_Pow_Absorb;

    function Lemma_Minus_Factor (X : T_Ref;
                                 Y : T_Ref) return Boolean
    is
        Z1 : T_Ref := X - Y;
        Z2 : T_Ref := X + (-1) * Y;
    begin
        pragma Assert (Z1 = Z2);
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
                                 A : Big_Natural;
                                 B : Big_Natural) return Boolean
    is 
    begin
        if B = 0 then
            pragma Assert (X ** (A + B) = (X ** A) * (X ** B));
        else
            declare 
                Induction_Hypothesis : Boolean := Lemma_Pow_Additive (X, A + 1, B - 1);
            begin
                pragma Assert (X ** (A + 1) * X ** (B - 1) = X ** (A + B));
                pragma Assert (((X ** A) * X) * X ** (B - 1) = X ** (A + B));
                pragma Assert (By (((X ** A) * X) * (X ** (B - 1)) = X ** A * (X * (X ** (B - 1))), Lemma_Mult_Associative (X ** A, X, X ** (B - 1))));
            end;
        end if;
        return True;
    end Lemma_Pow_Additive;

    function Lemma_Pow_Mult (X : T_ref;
                             A : Big_Natural;
                             B : Big_Natural) return Boolean
    is
    begin
        if B = 0 then
            pragma Assert ((X ** A) ** B = X ** (A * B));
        else
            declare
                pragma Assert (B - 1 in Big_Natural);
                Induction_Hypothesis : Boolean := Lemma_Pow_Mult (X, A, B - 1);
            begin
                pragma Assert (A * (B - 1) in Big_Natural);
                pragma Assert ((X ** A) ** (B - 1) = X ** (A * (B - 1)));
                pragma Assert ((X ** A) ** (B - 1) * (X ** A) = X ** (A * (B - 1)) * (X ** A));
                pragma Assert (By (X ** (A * (B - 1)) * (X ** A) = X ** (A * (B - 1) + A), Lemma_Pow_Additive (X, A * (B - 1), A)));
                pragma Assert ((X ** A) ** (B - 1) * (X ** A) = X ** (A * B));

            end;
        end if;
        return True;
    end Lemma_Pow_Mult;



end RecursNTT;
