
pragma Extensions_Allowed (On);
with SumGen; use SumGen;
with RefMLKEM; use RefMLKEM.ZqRef;

package body RecursNTT
    with SPARK_Mode => On
is



    function NTT_Recurs (E : Array_Of_Zq;
                         Psi : T_Ref;
                         Length : Positive) return Array_Of_Zq
    is
        Res : Array_Of_Zq (0 .. Index_Ref (Length - 1));
    begin
        if Length = 1 then
            Res (0) := E (0);
        else
            declare 
                A : Array_Of_Zq (0 .. Index_Ref (Length / 2 - 1));
                B : Array_Of_Zq (0 .. Index_Ref (Length / 2 - 1));
                package Splitter is new Generic_Split_Sum (T_Ref, Index_Ref, Array_Of_Zq);
            begin
                pragma Assert (Is_Pow_Of_Two (Length));
                pragma Assert (Length mod 2 = 0);
                pragma Assert ((Length / 2) = 1 or (Length / 2) mod 2 = 0);
                A := NTT_Recurs(Splitter.Extract_Even (E, Length), Psi * Psi, Length / 2);
                B := NTT_Recurs(Splitter.Extract_Odd (E, Length), Psi * Psi, Length / 2);
                for J in 0 .. (Length / 2 - 1) loop
                    Res (Index_Ref (J)) := A (Index_Ref (J)) + Psi ** (2 * J + 1) * B (Index_Ref (J));
                    Res (Index_Ref (J + Length / 2)) := A (Index_Ref (J)) - Psi ** (2 * J + 1) * B (Index_Ref (J));
                end loop;
            end;
        end if;
        return Res;
    end NTT_Recurs;

end RecursNTT;