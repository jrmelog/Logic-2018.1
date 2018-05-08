theory projeto2
imports Main

begin
theorem prova1:
  assumes p_qr: "P \<or> (Q\<and>R)"
  shows "(P\<or>Q) \<and> (P\<or>R)"

  proof -
    have p_pq_and_pr: "P \<Longrightarrow>(P\<or>Q) \<and> (P\<or>R)"
    proof -
      assume p: "P"
      from p have pq: "(P\<or>Q)" by (rule disjI1)
      from p have pr: "(P\<or>R)" by (rule disjI1)
      from pq and pr show "(P\<or>Q) \<and> (P\<or>R)" by (rule conjI)
    qed
    
    have qr_pq_and_pr: "(Q\<and>R) \<Longrightarrow>(P\<or>Q) \<and> (P\<or>R)"
    proof -
      assume qr:"(Q\<and>R)"
      from qr have q: "Q" by (rule conjE)
      from qr have r: "R" by (rule conjE)
      from q have pq: "(P\<or>Q)" by (rule disjI2)
      from r have pr: "(P\<or>R)" by (rule disjI2)
      from pq and pr show "(P\<or>Q) \<and> (P\<or>R)" by (rule conjI)
    qed
  from p_qr and p_pq_and_pr and qr_pq_and_pr show "(P\<or>Q)\<and>(P\<or>R)" by (rule disjE)
qed
end
