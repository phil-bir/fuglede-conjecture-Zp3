import itertools

from time import clock

import sys

from collections import Counter
from datetime import datetime
from copy import deepcopy


def stacks_from_davey(dmat):
  """
  Takes a Davey matrix dmat and returns
  it in 'stack' format.
  """
  p=len(dmat)
  stacks=[]
  for i in range(p):
    a=[]
    for j in range(p):
      a+=dmat[j][i]*[j]
    stacks.append(a)
  return stacks

def davey_on_vec(dmat,bvec):
  """
  Taking Davey matrix dmat and balanced vector bvec
  returns one possible balanced vector b such that
  dmac is raised by (bvec,b).
  """
  stacks=stacks_from_davey(dmat)
  b=[stacks[x].pop() for x in bvec]
  return b

def davey_on_vec_2x2(dmat1,bvec1,dmat2,bvec2):
  """
  Input: dmat1, bvec1, dmat2, bvec2
  Taking balanced vectors bvec1 and bvec2 as well as
  Davey matrices dmat1 and dmat2, returns all balanced
  vectors b3 such that bvec1, b3 give raise to dmat1
  and bvec2, b3 give raise to dmat2.
  """
  pn=len(bvec1)

  stacks1_=stacks_from_davey(dmat1)
  stacks2_=stacks_from_davey(dmat2)
  unresolved_=range(pn)
  result_=[0]*pn

  out=[]

  queue=[(stacks1_,stacks2_,unresolved_,result_)]

  guess=False
  guessed=False
  while len(queue)>0:
    stacks1,stacks2,unresolved,result=queue.pop(0)
    branch=False
    while len(unresolved)>0:
      resolved=[]
      for i in unresolved:
        s=set(stacks1[bvec1[i]]).intersection(stacks2[bvec2[i]])
        if (len(s)==0):
          unresolved=[]
          resolved=[]
          result=[]
          break
        if (len(s)==1 or branch):
          v=s.pop()
          if branch:
            for w in s:
              result_c=list(result)
              unresolved_c=list(unresolved)
              stacks1_c=list(map(list,stacks1))
              stacks2_c=list(map(list,stacks2))

              unresolved_c.remove(i)
              result_c[i]=w
              stacks1_c[bvec1[i]].remove(w)
              stacks2_c[bvec2[i]].remove(w)
              queue.append((stacks1_c,stacks2_c,unresolved_c,result_c))

          result[i]=v
          stacks1[bvec1[i]].remove(v)
          stacks2[bvec2[i]].remove(v)
          resolved+=[i]
          branch=False
      if len(resolved)>0:
        for j in resolved:
          unresolved.remove(j)
      else:
        #we have to branch somewhere
        branch=True

    if len(result)>0:
      out.append(result)

  return out


def get_davey_matrices(p,n):
  """
  Takes prime p and integer n and returns all Davey matrices mod p
  of weight n.
  """
  perm_dict={}
  for perm in itertools.permutations(range(p)):
    mat=[p*[0] for i in range(p)]
    for i in range(p):
      mat[i][perm[i]]=1
    key=tuple(sum([mat[j][(j+i)%p] for j in range(p)])
        for i in range(p))
    perm_dict[key]=perm_dict.get(key,[])+[mat]

  print "# of different permutation matrices: "+str(len(perm_dict))
  res=set()
  test=p*[n]
  time1=clock()
  for diag_sums in itertools.combinations_with_replacement(
      perm_dict,n):
    if [sum([diag_sums[j][i] for j in range(len(diag_sums))])
        for i in range(p)]==test:
      m=[perm_dict[diag_sums[i]] for i in range(n)]
      for s in itertools.product(*m):
        matrix=[[sum([s[i][j][k] for i in range(len(s))])
            for k in range(p)] for j in range(p)]
        res.add(tuple(map(tuple, matrix)))

  print "# of Davey matrices: "+str(len(res))


  print "time in sec: "+str(clock()-time1)


  return res



def balanced_linear_combinations(b1,b2,b3,p):
  """
  Takes balanced vectors b1, b2 and b3 (mod p) and
  returns a list of triples of numbers (u,v,w)
  such that b1*u+b2*v+b3*w is a balanced vector again.
  """
  test=[(i*p)/len(b1) for i in range(len(b1))]
  ret=[]
  for u,v,w in itertools.product(range(p),repeat=3):
    lcv=[(b1[i]*u+b2[i]*v+b3[i]*w)%p for i in range(len(b1))]
    if (sorted(lcv)==test):
      ret+=[(u,v,w)]
  return ret


def reduced_set(X,p,d=3):
  """
  Input:
  X list of tuples
  p prime
  Returns a sublist of X excluding entries that cannot be
  part of the solution.
  """
  redX=[]
  for e in X:
    add=True
    for i in range(d):
      s=list(e)
      s[i]=(s[i]-1)%p
      if not tuple(s) in X:
        add=False
        break
    if add:
      redX+=[e]
  return redX

def potential_solutions(A,X,size,p):
  mat=[
    [
      1 if (tuple((a[i]-b[i])%p for i in range(len(a))) in X) else 0
      for a in A
    ]
    for b in A
  ]
  rowsum=[sum(mat[i]) for i in range(len(mat))]
  candidates=[A[i] for i in range(len(rowsum)) if rowsum[i]>=size]
  return candidates

def davey_filtered_from_cache(davey_matrix,
    davey_encoded,davey_cache,p):
  davey_filtered=None
  for j in range(p):
    cs=tuple(
        itertools.chain.from_iterable(
        [davey_matrix[i][j]*[i] for i in range(p)]))
    if davey_filtered==None:
      davey_filtered=davey_cache[(davey_encoded[j],cs)].copy()
    else:
      davey_filtered&=davey_cache[(davey_encoded[j],cs)]
  return davey_filtered

def inner_loop(dx,p,n,b1,davey_cache,davey):
  #dimension d is 3, only works for this value
  d=3
  clique_size=p*n-4
  time_step=clock()
  count_reduced_set=Counter()
  count_nr_2x2_davey=Counter()
  most_candidates=0
  most_candidates_info=[]

  m=deepcopy(davey[dx]) #deep copy
  if m[0][1]==0:
    print "############ skip "+str(dx)+" #############"
    return []
  else:
    m[0][1]-=1

  print "+++++++++++++++++++++++++++++++++++++++++++++++"
  print "l = "+str(dx)

  # We can assume that b2[1]=0 from the assumption that b2
  # is lin indep of b1 (b1[1]=1).
  b2=[0,0]+davey_on_vec(m,b1[2:])


  davey_encoded=[tuple(itertools.chain.from_iterable(
      [davey[dx][j][i]*[i] for i in range(p)]))for j in range(p)]

  for dy in range(len(davey)):
    davey_filtered=davey_filtered_from_cache(
        davey[dy],davey_encoded,davey_cache,p)


    for dz in davey_filtered:
      davey_solutions=davey_on_vec_2x2(davey[dz],b1[1:],
          davey[dy],b2[1:])
      count_nr_2x2_davey[len(davey_solutions)]+=1
      for sol in davey_solutions:
        b3=[0]+sol
        valid_combinations=balanced_linear_combinations(b1,b2,b3,p)
        reduced_valid_comb=reduced_set(valid_combinations,p)
        count_reduced_set[len(reduced_valid_comb)]+=1
        if len(reduced_valid_comb)>=clique_size:
            clique_candidates=potential_solutions(
                reduced_valid_comb,valid_combinations,clique_size,p)
            if len(clique_candidates)>most_candidates:
              most_candidates=len(clique_candidates)
              most_candidates_info=[0,dx,dy,dz,b2,b3]
            if (len(clique_candidates)>=clique_size):
              print "#############################################"
              print "###      potential solution found         ###"
              print "#############################################"
              print b1,b2,b3
              print dx,dy,dz
              print clique_candidates
              print "#############################################"


  #end of this davey matrix - report:
  print "time = "+str(datetime.now())
  print "delta time = "+str(clock()-time_step)
  print "Davey 2x2 solutions: "+str(
      sorted(count_nr_2x2_davey.most_common()))
  print "rX sizes: "+str(sorted(count_reduced_set.most_common()))
  print "max row sum = "+str(most_candidates)
  print "max row info: "+str(most_candidates_info)


  return (
    count_nr_2x2_davey,
    count_reduced_set,
    most_candidates,
    most_candidates_info
  )

def calc_cache(p,n,davey_matrices):
  #do precalulations
  key_for_combination={}
  for i in range(p):
    for j in range(p):
      a=p*p*[0]
      a[p*j+i]=1
      key_for_combination[((j,),(i,))]=set([tuple(a)])



  for k in range(2,n+1):
    for t1 in itertools.combinations_with_replacement(range(p),k):
      for t2 in itertools.combinations_with_replacement(range(p),k):
        keys=set()
        for i in range(k):
          a=p*p*[0]
          a[p*t1[0]+t2[i]]=1
          for b in key_for_combination[(t1[1:],t2[:i]+t2[i+1:])]:
            keys.add(tuple([a[j]+b[j] for j in range(p*p)]))
        key_for_combination[(t1,t2)]=keys

  davey_matching={}
  for combination in key_for_combination:
    davey_matching[combination]=set()
    for d_idx in range(len(davey_matrices)):
      for key in key_for_combination[combination]:
        match=True
        for i in range(p*p):
          if davey_matrices[d_idx][i%p][i/p]<key[i]:
            match=False
            break
        if match:
          davey_matching[combination].add(d_idx)
          break
  return davey_matching


def counterexample_d3(p,n,start=0, end=0):
  # dimension d is 3, program only works for this value,
  # so value of d cannot be changed
  d=3

  davey=[]

  #subtract 1 from (0,0) for assumption that first column is 0-vector
  #we can also exclude all matrices with entry (0,0) being equal to 0.
  for dav in get_davey_matrices(p,n):
    e=list(map(list,dav))
    if e[0][0]>0:
      e[0][0]-=1
      davey.append(e)

  #sorting so search can be done in parts.
  davey.sort()
  print len(davey)

  time_start=clock()
  davey_matching=calc_cache(p,n,davey)


  print "cache calc done in "+str(clock()-time_start)
  print len(davey_matching)

  b1=n*range(p)

  bestX=[]
  best=[]
  maxRX=0
  print "==================================================="
  count_nr_2x2_davey_total=Counter()
  count_reduced_set_total=Counter()
  most_candidates_overall=0
  most_candidates_overall_info=[]

  time_start=clock()



  if end==0 or end>len(davey):
    end=len(davey)
  if start==0 or start<0:
    start=0

  for dx in range(start,end):
    #check if matrix should be skipped
    if davey[dx][0][1]==0:
      print "############ skip "+str(dx)+" #############"
    else:
      ret=inner_loop(dx,p,n,b1,davey_matching,davey)
      c2x2_davey,c_red_set,most_cand,most_cand_info=ret
      count_nr_2x2_davey_total+=c2x2_davey
      count_reduced_set_total+=c_red_set
      if most_cand>most_candidates_overall:
        most_candidates_overall=most_cand
        most_candidates_overall_info=most_cand_info


  print "==============================================="
  print "final report"
  print "time elapsed = "+str(clock()-time_start)
  print "Davey 2x2 solutions: "+str(sorted(
      count_nr_2x2_davey_total.most_common()))
  print "rX sizes: "+str(sorted(count_reduced_set_total.most_common()))
  print "max row sum = "+str(most_candidates_overall)
  print "max row info: "+str(most_candidates_overall_info)
  print "==============================================="


def main():
  if len(sys.argv)>=3:
    args=[int(sys.argv[i]) for i in range(1,len(sys.argv))]
    counterexample_d3(*args)
  else:
    sys.stderr.write("need arguments!\n")

  return 0

if __name__ == '__main__':
  main()

