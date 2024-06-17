with SumGen; use SumGen;
with RefMLKEM; use RefMLKEM.ZqRef;

package body RecursNTT
    with SPARK_Mode => On
is



    function NTT_Recurs (E : Array_Of_Zq;
                         Psi : T_Ref) return Array_Of_Zq
    is
        Res : Array_Of_Zq (0 .. Index_Ref (E'Length - 1)) with Relaxed_Initialization;
    begin
        if E'Length = 1 then
            Res (0) := E (0);
        else
            declare 
                A : Array_Of_Zq (0 .. Index_Ref (E'Length / 2 - 1));
                B : Array_Of_Zq (0 .. Index_Ref (E'Length / 2 - 1));
                package Summer is new Sum_On_Array (T_Ref, Index_Ref, Array_Of_Zq);
            begin
                pragma Assert (Is_Pow_Of_Two (E'Length));
                pragma Assert (E'Length mod 2 = 0);
                pragma Assert ((E'Length / 2) = 1 or (E'Length / 2) mod 2 = 0);
                A := NTT_Recurs(Summer.Extract_Even (E), Psi * Psi);
                B := NTT_Recurs(Summer.Extract_Odd (E), Psi * Psi);
                for J in 0 .. (E'Length / 2 - 1) loop
                    Res (Index_Ref (J)) := A (Index_Ref (J)) + Psi ** (2 * J + 1) * B (Index_Ref (J));
                    Res (Index_Ref (J + E'Length / 2)) := A (Index_Ref (J)) - Psi ** (2 * J + 1) * B (Index_Ref (J));
                    pragma Loop_Invariant (for all K in 0 .. J => 
                                            Res (Index_Ref (K))'Initialized
                                          );
                    pragma Loop_Invariant (for all K in E'Length / 2 .. E'Length / 2 + J => 
                                            Res (Index_Ref (K))'Initialized
                                          );
                end loop;
                pragma Assert (for all J in 0 .. (E'Length / 2 - 1) => Res (Index_Ref (J))'Initialized);
                pragma Assert (for all J in 0 .. (E'Length / 2 - 1) => Res (Index_Ref (J + E'Length / 2))'Initialized);
                pragma Assert (for all J in 0 .. (E'Length - 1) => Res (Index_Ref (J))'Initialized);
            end;
        end if;
        return Res;
    end NTT_Recurs;

end RecursNTT;