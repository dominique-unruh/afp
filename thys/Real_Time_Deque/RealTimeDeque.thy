section \<open>Real-Time Deque Implementation\<close>

theory RealTimeDeque
imports States
begin

text\<open>
The real-time deque can be in the following states:

 \<^descr> \<open>Empty\<close>: No values stored. No dequeue operation possible.
 \<^descr> \<open>One\<close>: One element in the deque.
 \<^descr> \<open>Two\<close>: Two elements in the deque.
 \<^descr> \<open>Three\<close>: Three elements in the deque.
 \<^descr> \<open>Idle\<close>: Deque with a left and a right end, fulfilling the following invariant:
   \<^item> 3 * size of left end \<open>\<ge>\<close> size of right end
   \<^item> 3 * size of right end \<open>\<ge>\<close> size of left end
   \<^item> Neither of the ends is empty
 \<^descr> \<open>Transforming\<close>: Deque which violated the invariant of the \<open>idle\<close> state by non-balanced dequeue and enqueue operations. The invariants during in this state are:
   \<^item> The transformation is not done yet. The deque needs to be in \<open>idle\<close> state otherwise.
   \<^item> The transformation is in a valid state (Defined in theory \<open>States\<close>)
   \<^item> The two ends of the deque are in a size window, such that after finishing the transformation the invariant of the \<open>idle\<close> state will be met. 

Functions:

 \<^descr> \<open>is_empty\<close>: Checks if a deque is in the \<open>Empty\<close> state
 \<^descr> \<open>deqL’\<close>: Dequeues an element on the left end and return the element and the deque without this element. If the deque is in \<open>idle\<close> state and the size invariant is violated either a \<open>transformation\<close> is started or if there are 3 or less elements left the respective states are used. On \<open>transformation\<close> start, six steps are executed initially. During \<open>transformation\<close> state four steps are executed and if it is finished the deque returns to \<open>idle\<close> state.
 \<^descr> \<open>deqL\<close>: Removes one element on the left end and only returns the new deque.
 \<^descr> \<open>firstL\<close>: Removes one element on the left end and only returns the element.
 \<^descr> \<open>enqL\<close>: Enqueues an element on the left and returns the resulting deque. Like in \<open>deqL'\<close> when violating the size invariant in \<open>idle\<close> state, a \<open>transformation\<close> with six initial steps is started. During \<open>transformation\<close> state four steps are executed and if it is finished the deque returns to \<open>idle\<close> state.
 \<^descr> \<open>swap\<close>: The two ends of the deque are swapped.
 \<^descr> \<open>deqR’\<close>, \<open>deqR\<close>, \<open>firstR\<close>, \<open>enqR\<close>: Same behaviour as the left-counterparts. Implemented using the left-counterparts by swapping the deque before and after the operation.
 \<^descr> \<open>listL\<close>, \<open>listR\<close>: Get all elements of the deque in a list starting at the left or right end. They are needed as list abstractions for the correctness proofs.
\<close>

datatype 'a deque =
    Empty
  | One 'a
  | Two 'a 'a
  | Three 'a 'a 'a 
  | Idle "'a idle" "'a idle"
  | Transforming "'a states"

definition empty where
  "empty \<equiv> Empty"

instantiation deque::(type) is_empty
begin

fun is_empty_deque :: "'a deque \<Rightarrow> bool" where
  "is_empty_deque Empty = True"
| "is_empty_deque _ = False"

instance..
end

fun swap :: "'a deque \<Rightarrow> 'a deque" where
  "swap Empty = Empty"  
| "swap (One x) = One x"
| "swap (Two x y) = Two y x"
| "swap (Three x y z) = Three z y x"
| "swap (Idle left right) = Idle right left"
| "swap (Transforming (States Left big small)) = (Transforming (States Right big small))"
| "swap (Transforming (States Right big small)) = (Transforming (States Left big small))"

fun small_deque :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a deque" where
  "small_deque []     [] = Empty"

| "small_deque (x#[]) [] = One x"
| "small_deque [] (x#[]) = One x"

| "small_deque (x#[])(y#[]) = Two y x"
| "small_deque (x#y#[]) [] = Two y x"
| "small_deque [] (x#y#[])= Two y x"

| "small_deque [] (x#y#z#[])   = Three z y x"
| "small_deque (x#y#z#[]) []   = Three z y x"
| "small_deque (x#y#[]) (z#[]) = Three z y x"
| "small_deque (x#[]) (y#z#[]) = Three z y x"

fun deqL' :: "'a deque \<Rightarrow> 'a * 'a deque" where
  "deqL' (One x) = (x, Empty)"
| "deqL' (Two x y) = (x, One y)"
| "deqL' (Three x y z) = (x, Two y z)"
| "deqL' (Idle left (idle.Idle right length_right)) = (
   case Idle.pop left of (x, (idle.Idle left length_left)) \<Rightarrow>
    if 3 * length_left \<ge> length_right 
    then 
      (x, Idle (idle.Idle left length_left) (idle.Idle right length_right))
    else if length_left \<ge> 1
    then 
      let length_left' = 2 * length_left + 1 in
      let length_right' = length_right - length_left - 1 in

      let small  = Reverse1 (Current [] 0 left length_left') left [] in
      let big = Reverse (Current [] 0 right length_right') right [] length_right' in

      let states = States Left big small in
      let states = (step^^6) states in
      
      (x, Transforming states)
    else 
      case right of Stack r1 r2 \<Rightarrow> (x, small_deque r1 r2)
  )"
| "deqL' (Transforming (States Left big small)) = (
    let (x, small) = Small.pop small in 
    let states = (step^^4) (States Left big small) in
    case states of 
        States Left
          (Big.Common (Common.Idle _ big))
          (Small.Common (Common.Idle _ small)) 
           \<Rightarrow> (x, Idle small big)
     | _ \<Rightarrow> (x, Transforming states)
  )"
| "deqL' (Transforming (States Right big small)) = (
    let (x, big) = Big.pop big in 
    let states = (step^^4) (States Right big small) in
    case states of 
       States Right 
          (Big.Common (Common.Idle _ big)) 
          (Small.Common (Common.Idle _ small)) \<Rightarrow>
            (x, Idle big small)
     | _ \<Rightarrow> (x, Transforming states)
  )"

fun deqR' :: "'a deque \<Rightarrow> 'a * 'a deque" where
  "deqR' deque = (
    let (x, deque) = deqL' (swap deque) 
    in (x, swap deque)
  )"

fun deqL :: "'a deque \<Rightarrow> 'a deque" where
  "deqL deque = (let (_, deque) = deqL' deque in deque)"

fun deqR :: "'a deque \<Rightarrow> 'a deque" where
  "deqR deque = (let (_, deque) = deqR' deque in deque)"

fun firstL :: "'a deque \<Rightarrow> 'a" where
  "firstL deque = (let (x, _) = deqL' deque in x)" 

fun firstR :: "'a deque \<Rightarrow> 'a" where
  "firstR deque = (let (x, _) = deqR' deque in x)" 

fun enqL :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqL x Empty = One x"
| "enqL x (One y) = Two x y"
| "enqL x (Two y z) = Three x y z"
| "enqL x (Three a b c) = Idle (idle.Idle (Stack [x, a] []) 2) (idle.Idle (Stack [c, b] []) 2)"
| "enqL x (Idle left (idle.Idle right length_right)) = (
    case Idle.push x left of idle.Idle left length_left \<Rightarrow> 
      if 3 * length_right \<ge> length_left
      then 
        Idle (idle.Idle left length_left) (idle.Idle right length_right)
      else 
        let length_left = length_left - length_right - 1 in
        let length_right = 2 * length_right + 1 in

        let big  = Reverse  (Current [] 0 left length_left) left [] length_left in
        let small = Reverse1 (Current [] 0 right length_right) right [] in
  
        let states = States Right big small in
        let states = (step^^6) states in
        
        Transforming states
  )"
| "enqL x (Transforming (States Left big small)) = (
    let small = Small.push x small in 
    let states = (step^^4) (States Left big small) in
    case states of 
        States Left 
          (Big.Common (Common.Idle _ big))
          (Small.Common (Common.Idle _ small)) 
         \<Rightarrow> Idle small big
     | _ \<Rightarrow> Transforming states
  )"
| "enqL x (Transforming (States Right big small)) = (
    let big = Big.push x big in 
    let states = (step^^4) (States Right big small) in
    case states of 
        States Right 
          (Big.Common (Common.Idle _ big)) 
          (Small.Common (Common.Idle _ small)) 
         \<Rightarrow> Idle big small
     | _ \<Rightarrow> Transforming states
  )"

fun enqR :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqR x deque = (
    let deque = enqL x (swap deque) 
    in swap deque
  )"    
 
fun listL :: "'a deque \<Rightarrow> 'a list" where
  "listL Empty = []"
| "listL (One x) = [x]"
| "listL (Two x y) = [x, y]"
| "listL (Three x y z) = [x, y, z]"
| "listL (Idle left right) = Idle.list left @ (rev (Idle.list right))"
| "listL (Transforming states) = States.listL states"

abbreviation listR :: "'a deque \<Rightarrow> 'a list" where
  "listR deque \<equiv> rev (listL deque)"

instantiation deque::(type) invar
begin

fun invar_deque :: "'a deque \<Rightarrow> bool" where
  "invar Empty = True"
| "invar (One _) = True"
| "invar (Two _ _) = True"
| "invar (Three _ _ _) = True"
| "invar (Idle left right) \<longleftrightarrow>
   invar left  \<and>
   invar right \<and>
   \<not> is_empty left  \<and> 
   \<not> is_empty right \<and>
   3 * size right \<ge> size left \<and>
   3 * size left \<ge> size right
  "
| "invar (Transforming states) \<longleftrightarrow> 
   invar states \<and>
   size_ok states \<and>
   0 < remaining_steps states
  "

instance..
end

end
