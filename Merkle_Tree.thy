theory Merkle_Tree
  imports "HOL-Library.Tree"
begin 

(*This theory file implements Merkle Tree Data Structure
Merkle Trees are widely used in blockchain technologies.
Numerous transactions are stored in a block and inquiring whether 
a given  transaction is in the block or not is common operation. 
Merkle trees allow us to give a 'proof of membership' of a given transaction,
 which can be verified efficiently. 

Merkle trees also enable us to check the authenticity of a given block. 
Merkle root is stored in the block header and whenever a transaction 
is replaced, merkle root changes as well.*)


(*A cryptographic hash function is compulsory to implement a merkle tree.
We will work with a locale and use a general hash function here.*)
type_synonym hash = "bool list"
type_synonym merkle = "hash tree"

locale merkle_tree =
  fixes hash_func :: "bool list \<Rightarrow> hash"
begin

  (*Combines two given merkle trees*)
  fun hashing_trees :: "hash tree \<Rightarrow> hash tree \<Rightarrow> hash" where
"hashing_trees Leaf Leaf = undefined"|
"hashing_trees (Node t1 h t2) Leaf = ( (hash_func (h@h)))"|
"hashing_trees Leaf (Node t1 h t2) = ( (hash_func (h@h)))"|
"hashing_trees (Node t11 h1 t12) (Node t21 h2 t22) = ( (hash_func (h1@h2)))"

(*A merkle tree is basically a binary tree of hashes, 
where each node stores the hash of the concatenation of its children.*)
fun valid_merkle :: "merkle \<Rightarrow> bool" where
"valid_merkle Leaf = True"|
"valid_merkle (Node m1 h m2) = (if (m1=Leaf \<and> m2=Leaf) then True else 
                              (valid_merkle m1 \<and>
                               valid_merkle m2 \<and>
                               (hashing_trees m1 m2 = h)))"

  (*Merkle tree generation from a given list.*)
  (*Given a list of transaction, we will construct the corresponding merkle tree.*)

  (*We will map the hash of each transaction to one node merkle tree. 
    Then we will recursively construct the merkle trees from the list.*)
  fun mapto_tree :: "hash list \<Rightarrow> merkle list" where
    "mapto_tree xs = map (\<lambda> x. (Node Leaf x Leaf)) xs"
  (*phc stands for "pair-hash-combine"*)  
  (* Pair contiguous merkle trees and combine them*)
  fun phc :: "merkle list \<Rightarrow> merkle list" where
    "phc [] = []" |
    "phc [m] = [Node m (hashing_trees m m) m]" |
    "phc (m1  # m2 # xs) = (Node m1  (hashing_trees m1 m2) m2) # phc xs"

  (*The following two lemmas are to prove termination of the next function.*)
  lemma term1:"length (phc ls) \<le> length ls"
    apply(induction ls rule:phc.induct)
      apply(auto)
    done
  lemma term2: "ls = (x#y#xs) \<Longrightarrow> length (phc ls) < length ls"
    apply(induction ls rule:phc.induct)
      apply(auto)
    by (simp add: term1 le_imp_less_Suc)

  (*Apply pair-hash-combine until there is only one element left in the list. 
  This is the final merkle tree.*)
  function gen_merk_wphc_fm :: "merkle list \<Rightarrow> merkle" where
    "gen_merk_wphc_fm [] = Leaf"|
    "gen_merk_wphc_fm [m] = m"|
    "gen_merk_wphc_fm (m1#m2#m) = gen_merk_wphc_fm (phc (m1#m2#m))"
    apply(auto)
    by (metis list.exhaust)

  termination gen_merk_wphc_fm 
    apply(auto) 
    by (meson "termination" term2 mlex_less wf_empty wf_mlex)
  (*gen_merk_wphc_fm function takes a list of merkle trees, 
    we abbreviate the following function to apply to the list 
    of the hashes of transactions.*)
  abbreviation "gen_merkle_wphc \<equiv> gen_merk_wphc_fm\<circ>mapto_tree"

  (*To prove correction lemmas, we will need the following function.
  Returns true if all the merkle trees are valid in a list.*)
  fun all_valid :: "merkle list \<Rightarrow> bool" where
    "all_valid [] = True"|
    "all_valid (m#ms) = (valid_merkle m \<and> all_valid ms)"

(*mapto_tree creates valid merkle trees.*)
lemma VM: "all_valid (mapto_tree xs)"
  apply(induction xs)
   apply(auto)
  done

(*pair-hash-combine preserves validness.*)
lemma VP: "all_valid xs \<Longrightarrow> all_valid (phc xs)"
  apply(induction xs rule:phc.induct)
    apply(auto)
  done

(*gen_merk preserves validness.*)
lemma VG: "all_valid xs \<Longrightarrow> valid_merkle (gen_merk_wphc_fm xs)"
proof (induction xs rule:length_induct)
  case (1 xs)
  then show ?case 
proof (cases xs rule:gen_merk_wphc_fm.cases)
  case 1
  then show ?thesis by auto
next
  case (2 m)
  then show ?thesis 
    using "1.prems" by auto
next
  case (3 m1 m2 m)
  then show ?thesis using term2 "1.IH" "1.prems" VP gen_merk_wphc_fm.simps(3) by presburger
qed
qed

(*gen_merkle creates valid merkle trees.*)
lemma "valid_merkle(gen_merkle_wphc xs)" using VM VP VG by simp
  

(*Validation of a membership proof*)

(*A membership proof is basically a path from the leaf of the given transaction to the root.
When this path is followed by concatinating and hashing, if the same merkle root is reached, 
then the proof is verified. 
This merkle path can be encoded with a list of tuples of hashes and direction. 
Direction informs us on which side to concat the hashes.*)
datatype D = L | R
fun follow_mpath :: "hash \<Rightarrow> (hash \<times> D) list \<Rightarrow> hash" where
"follow_mpath h [] = h" |
"follow_mpath h ((h', d)#xs) = (case d of L \<Rightarrow> follow_mpath (hash_func (h'@h)) xs |
                                      R \<Rightarrow> follow_mpath (hash_func (h@h')) xs)"

fun validate :: "hash \<Rightarrow> (hash \<times> D) list \<Rightarrow> hash \<Rightarrow> bool" where
"validate h path merkle_root = (follow_mpath h path = merkle_root)"

(*Generation of a membership proof*)
(*The merkle path of a given transaction can be directly calculated by its index.*)
(*In the first step, if the index of the transacion is even,
then it will be hashed with the Right neighbor, if it's odd then it is the left neighbor.
The following steps are recursively applied to the paired-hashed list.*)
fun ph :: "hash list \<Rightarrow> hash list" where
    "ph [] = []" |
    "ph [m] = [hash_func (m@m)]" |
    "ph (m1  # m2 # xs) = (hash_func (m1@m2)) # ph xs"

  (*The following two lemmas are to prove termination of the next function.*)
  lemma term1_ph:"length (ph ls) \<le> length ls"
    apply(induction ls rule:ph.induct)
      apply(auto)
    done
  lemma term2_ph: "ls = (x#y#xs) \<Longrightarrow> length (ph ls) < length ls"
    apply(induction ls rule:ph.induct)
      apply(auto)
    by (simp add: term1_ph le_imp_less_Suc)

(*Notice that if the even index i is in the last, then there is no i+1. 
In this case, element will be hashed with itself.*)
function generate_path_wi :: "nat \<Rightarrow> hash list \<Rightarrow> (hash \<times> D) list" where
"generate_path_wi i [] = []"|
"generate_path_wi i [h] = []"|
"generate_path_wi i (h1#h2#hs) = (
                            (if i mod 2 = 0 then 
                              ( nth (h1#h2#hs) (if i=length (h1#h2#hs) -1 
                                                then i else (i+1)), R) 
                            
                            else (nth (h1#h2#hs) (i-1), L))
                            # 
                            (generate_path_wi (i div 2) (ph (h1#h2#hs)))
                         )"
  apply(auto)
  by (metis list.exhaust)

termination generate_path_wi
  apply(auto)
  sorry

(*I couldn't import List_Index library somehow.*)
fun index :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"index [] x = undefined"|
"index (h#hs) x = (if h=x then 0 else (index hs x + 1))"


fun generate_path :: "hash \<Rightarrow> hash list \<Rightarrow> (hash \<times> D) list" where
"generate_path h hl = generate_path_wi (index hl h) hl"

function find_merkle_root_fh :: "hash list \<Rightarrow> hash" where
"find_merkle_root_fh [] = undefined"|
"find_merkle_root_fh [x] =  x"|
"find_merkle_root_fh (x#y#xs) = find_merkle_root_fh (ph (x#y#xs))"
apply(auto)
  using ph.cases by blast

termination find_merkle_root_fh
apply(auto)
  by (meson "termination" term2_ph mlex_less wf_empty wf_mlex)

(*Prove that generate_path works correctly.*)                        
lemma "(nth hl i) \<in> set hl \<Longrightarrow>  validate (nth hl i) (generate_path_wi i hl) (find_merkle_root_fh hl)"
  apply(induction i hl rule:generate_path_wi.induct)
   apply(auto)
  sorry

lemma "h \<in> set  hl \<Longrightarrow> validate h (generate_path h hl) (find_merkle_root_fh hl)"
  apply(auto)
  sorry


end

end