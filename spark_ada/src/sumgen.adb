
with SPARK.Cut_Operations; use SPARK.Cut_Operations;

package body SumGen 
    with SPARK_Mode => On
is

    function Is_Pow_Of_Two (A : Positive) return Boolean
    is
        (A mod 2 = 0 and Is_Pow_Of_Two (A / 2));

    package body Sum_On_Array is 

        function Cut_Last (A : ArrayType) return ArrayType
        is
            Res : ArrayType (A'First .. A'Last - 1) with Relaxed_Initialization;
        begin
            for I in A'First .. A'Last - 1 loop
                Res (I) := A (I);
                pragma Loop_Invariant (for all J in A'First .. I => (
                                            Res(J)'Initialized and
                                            Res(J) = A(J)
                                       ));
            end loop;
            return Res;
        end Cut_Last;

        function Partial_Sum (A : ArrayType;
                              Max_Index : IndexRange) return ElementType
        is (if Max_Index = 0 then A (0) else Partial_Sum (A, Max_Index - 1) + A (Max_Index));

        function "+" (F : ArrayType;
                      G : ArrayType) return ArrayType
        is
            Res : ArrayType (F'Range) with Relaxed_Initialization;
        begin
            for I in F'Range loop
                Res (I) := F (I) + G (I);
                pragma Loop_Invariant (for all J in 0 .. I => 
                                        Res(J)'Initialized and then 
                                        (Res (J) = F (J) + G (J)));
            end loop;
            return Res;
        end "+";

        function Lemma_Partial_Sum_Disjoint (F : ArrayType;
                                     G : ArrayType;
                                     Max_Index : IndexRange) return Boolean
        is
            H : ArrayType := F + G;
            Tiny_Sum_F : ElementType;
            Tiny_Sum_G : ElementType;
            Tiny_Sum_H : ElementType;
            Induction_Hypothesis : Boolean;
            Sum_F : ElementType := Partial_Sum (F, Max_Index);
            Sum_G : ElementType := Partial_Sum (G, Max_Index);
            Sum_H : ElementType := Partial_Sum (H, Max_Index);
        begin
            if (Max_Index = 0) then
                pragma Assert (Sum_F + Sum_G = Sum_H);
            elsif (Max_Index > 0) then
                Tiny_Sum_F := Partial_Sum (F, Max_Index - 1); 
                pragma Assert (Sum_F = Tiny_Sum_F + F (Max_Index));
                Tiny_Sum_G := Partial_Sum (G, Max_Index - 1); 
                pragma Assert (Sum_G = Tiny_Sum_G + G (Max_Index));
                Tiny_Sum_H := Partial_Sum (H, Max_Index - 1); 
                pragma Assert (Sum_H = Tiny_Sum_H + H (Max_Index));

                Induction_Hypothesis := Lemma_Partial_Sum_Disjoint (F, G, Max_Index - 1);

                pragma Assert (By (Tiny_Sum_F + Tiny_Sum_G = Tiny_Sum_H, Induction_Hypothesis));

                pragma Assert (F (Max_Index) + G (Max_Index) = H (Max_Index));
                pragma Assert ((Tiny_Sum_F + Tiny_Sum_G) + (F (Max_Index) + G (Max_Index)) = Tiny_Sum_H + H (Max_Index));
                pragma Assert (By (
                    (Tiny_Sum_F + Tiny_Sum_G) + (F (Max_Index) + G (Max_Index)) = (((Tiny_Sum_F + Tiny_Sum_G) + F (Max_Index)) + G (Max_Index)),
                    Lemma_Add_Associative (Tiny_Sum_F + Tiny_Sum_G, F (Max_Index), G (Max_Index))
                ));
                pragma Assert (By (
                    ((Tiny_Sum_F + Tiny_Sum_G) + F (Max_Index)) + G (Max_Index) = (Tiny_Sum_F + (Tiny_Sum_G + F (Max_Index))) + G (Max_Index),
                    Lemma_Add_Associative (Tiny_Sum_F, Tiny_Sum_G, F (Max_Index))
                ));
                pragma Assert (By (
                    (Tiny_Sum_F + (Tiny_Sum_G + F (Max_Index))) + G (Max_Index) = Tiny_Sum_F + (F (Max_Index)+ Tiny_Sum_G) + G (Max_Index),
                    Lemma_Add_Commutative (F (Max_Index), Tiny_Sum_G)
                ));
                pragma Assert (By (
                    Tiny_Sum_F + (F (Max_Index)+ Tiny_Sum_G) + G (Max_Index) = ((Tiny_Sum_F + F (Max_Index)) + Tiny_Sum_G) + G (Max_Index),
                    Lemma_Add_Associative (Tiny_Sum_F, F(Max_Index), Tiny_Sum_G)
                ));
                pragma Assert (By (
                    ((Tiny_Sum_F + F (Max_Index)) + Tiny_Sum_G) + G (Max_Index) = (Tiny_Sum_F + F (Max_Index)) + (Tiny_Sum_G + G (Max_Index)),
                    Lemma_Add_Associative (Tiny_Sum_F + F (Max_Index), Tiny_Sum_G, G (Max_Index))
                ));
                pragma Assert ((Tiny_Sum_F + F (Max_Index))+ (Tiny_Sum_G + G (Max_Index)) = Tiny_Sum_H + H (Max_Index));
                pragma Assert (Sum_F + Sum_G = Sum_H);
            end if;
            return True;
        end Lemma_Partial_Sum_Disjoint;

        function Sum (A : ArrayType) return ElementType
        is
            (if A'Length = 0 then 0 elsif A'Length = 1 then A (0) else Sum (Cut_Last (A)) + A (A'Last));


        function Lemma_Add_Associative (A : ElementType;
                                        B : ElementType;
                                        C : ElementType) return Boolean
        is (True);

        function Lemma_Add_Commutative (A : ElementType;
                                        B : ElementType) return Boolean
        is (True);

        function Extract_Even (F : ArrayType) return ArrayType
        is 
            Res : ArrayType (0 .. IndexRange (F'Length / 2 - 1)) with Relaxed_Initialization;
        begin
            for I in 0 .. (F'Length / 2 - 1) loop
                Res (IndexRange (I)) := F (IndexRange (2 * I));
                pragma Loop_Invariant (for all J in 0 .. I => 
                    Res (IndexRange (J))'Initialized and
                    Res (IndexRange (J)) = F (IndexRange (2 * J))
                );
            end loop;
            return Res;
        end Extract_Even;

        function Extract_Odd (F : ArrayType) return ArrayType
        is 
            Res : ArrayType (0 .. IndexRange (F'Length / 2 - 1)) with Relaxed_Initialization;
        begin
            for I in 0 .. (F'Length / 2 - 1) loop
                Res (IndexRange (I)) := F (IndexRange (2 * I + 1));
                pragma Loop_Invariant (for all J in 0 .. I => 
                    Res (IndexRange (J))'Initialized and
                    Res (IndexRange (J)) = F (IndexRange (2 * J + 1))
                );
            end loop;
            return Res;
        end Extract_Odd;

        function Lemma_Split_Odd_Even (A :  ArrayType) return Boolean
        is
        begin
            pragma Assert (A'First = 0);
            pragma Assert (if A'Length = 1 then Sum (A) = A(0) );
            if (A'Length = 2) then
                pragma Assert (Extract_Even (A)'Length = 1);
                pragma Assert (Extract_Even (A)'Last = 0);
                pragma Assert (Sum (Extract_Even (A)) = Extract_Even (A)(Extract_Even (A)'Last));
                pragma Assert (Sum (Extract_Even (A)) = A (0));
                pragma Assert (Sum (A) = Sum (Extract_Even (A)) + Sum (Extract_Odd (A)));
            else
                declare
                    pragma Assert (A'Length > 2);
                    B : ArrayType := Cut_Last (Cut_Last (A));
                    Lemma_To_B : Boolean := Lemma_Split_Odd_Even (B);
                    Even_A : ArrayType := Extract_Even (A);
                    Odd_A : ArrayType := Extract_Odd (A);
                    Even_B : ArrayType := Extract_Even (B);
                    Odd_B : ArrayType := Extract_Odd (B);
                begin
                    pragma Assert (By (Sum (B) = Sum (Even_B) + Sum (Odd_B), Lemma_To_B));

                    pragma Assert (for all I in Even_B'First .. Even_B'Last => (
                        Cut_Last (Even_A) (I) = Even_B (I)
                    ));
                    pragma Assert (Cut_Last (Even_A) = Even_B);
                    pragma Assert (By (Sum (Cut_Last (Even_A)) = Sum (Even_B), Lemma_Sum_Extensional (Cut_Last (Even_A), Even_B)));
                    pragma Assert (Even_A (Even_A'Last) = A (A'Last - 1));
                    pragma Assert (Sum (Even_A) = Sum (Even_B) + A (A'Last - 1));

                    pragma Assert (for all I in Odd_B'First .. Odd_B'Last => (
                        Cut_Last (Odd_A) (I) = Odd_B (I)
                    ));
                    pragma Assert (Cut_Last (Odd_A) = Odd_B);
                    pragma Assert (By (Sum (Cut_Last (Odd_A)) = Sum (Odd_B), Lemma_Sum_Extensional (Cut_Last (Odd_A), Odd_B)));
                    pragma Assert (Odd_A (Extract_Odd (A)'Last) = A (A'Last));
                    pragma Assert (Sum (Odd_A) = Sum (Odd_B) + A (A'Last));

                    pragma Assert (Sum (A) = Sum (Cut_Last (A)) + A (A'Last));
                    pragma Assert (Sum (Cut_Last (A)) = Sum (B) + A (A'Last - 1));
                    pragma Assert (Sum (A) = Sum (B) + A (A'Last - 1) + A (A'Last));

                    pragma Assert (Sum (A) = ((Sum (Even_B) + Sum (Odd_B)) + A (A'Last - 1)) + A (A'Last));
                    pragma Assert (By (
                            ((Sum (Even_B) + Sum (Odd_B)) + A (A'Last - 1)) + A (A'Last) = (Sum (Even_B) + (Sum (Odd_B) + A (A'Last - 1))) + A (A'Last),
                            Lemma_Add_Associative (Sum (Even_B), Sum (Odd_B), A (A'Last - 1))
                    ));
                    
                    pragma Assert (By (
                            (Sum (Even_B) + (Sum (Odd_B) + A (A'Last - 1))) + A (A'Last) = (Sum (Even_B) + (A (A'Last - 1) + Sum (Odd_B))) + A (A'Last),
                            Lemma_Add_Commutative (A (A'Last - 1), Sum (Odd_B))
                    ));

                    pragma Assert (By (
                            (Sum (Even_B) + (A (A'Last - 1) + Sum (Odd_B))) + A (A'Last) = ((Sum (Even_B) + A (A'Last - 1)) + Sum (Odd_B)) + A (A'Last),
                            Lemma_Add_Associative (Sum (Even_B), A (A'Last - 1), Sum (Odd_B))
                    ));

                    pragma Assert (By (
                            ((Sum (Even_B) + A (A'Last - 1)) + Sum (Odd_B)) + A (A'Last) = (Sum (Even_B) + A (A'Last - 1)) + (Sum (Odd_B) + A (A'Last)),
                            Lemma_Add_Associative (Sum (Even_B) + A (A'Last - 1), Sum (Odd_B), A (A'Last))
                    ));

                    pragma Assert (Sum (A) = Sum (Even_A) + Sum (Odd_A));
                end;
            end if;
            return True;
        end Lemma_Split_Odd_Even;

        function Lemma_Sum_Extensional (A : ArrayType;
                                        B : ArrayType) return Boolean
        is
        begin
            if A'Length <= 1 then
                pragma Assert (Sum (A) = Sum (B));
            else
                declare
                    Induction_Hypothesis : Boolean := Lemma_Sum_Extensional (Cut_Last (A), Cut_Last (B));
                begin
                    pragma Assert (By (Sum (A) = Sum (B), Induction_Hypothesis));
                end;
            end if;
            return True;
        end Lemma_Sum_Extensional;

    end Sum_On_Array;

    package body Generic_Apply_To_Array is
        function Apply_To_Array (X : InputTypeA) return InputTypeB
        is
            Res : InputTypeB;
        begin
            for I in IndexRange loop
                Res (I) := Func (X (I));
            end loop;
            return Res;
        end Apply_To_Array;
    end Generic_Apply_To_Array;

end SumGen;