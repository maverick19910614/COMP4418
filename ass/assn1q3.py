# -*- coding: utf-8 -*-
"""
Created on Wed Oct  9 20:25:20 2019

@author: Maverick
"""
#! /usr/bin/ env python
from sys import argv

sequent = '[[p iff q] seq [(q iff r) imp (p iff r)]]'

#sequent=argv[1]
seq=sequent.replace('[','')
seq=seq.replace(']','')
seq=seq.replace('neg','¬')
seq=seq.replace('and','∧')
seq=seq.replace('or','∨')
seq=seq.replace('imp','→')
seq=seq.replace('iff','↔')
seq=seq.replace('seq','⊢')
seq=seq.split('⊢')
count_left=0
count_right=0
check=0
l_braket_nb=0
for i in seq[0]:
    if i == '(':
       l_braket_nb+=1
       
r_braket_nb=0
for i in seq[1]:
    if i == '(':
       r_braket_nb+=1
list_count=0
list_braket=dict()
braket_include=dict()
braket_count=l_braket_nb
ll=0
lr=0

# =============================================================================
# braket 
# =============================================================================

while braket_count:
    ll=seq[0].index('(')
    for i in range(ll+1,len(seq[0])):
        if seq[0][i]=='(':
            ll=i
        if seq[0][i] == ')':
            lr=i
            list_braket[list_count]=seq[0][ll+1:lr]
            braket_include[list_count]=seq[0][ll:lr+1]
            seq[0]=seq[0].replace(seq[0][ll:lr+1],str(list_count))
            list_count+=1
            break
    braket_count-=1
braket_count=r_braket_nb
rl=0
rr=0
while braket_count:
    rl=seq[1].index('(')
    for i in range(rl+1,len(seq[1])):
        if seq[1][i]=='(':
            rl=i
        if seq[1][i] == ')':
            rr=i
            list_braket[list_count]=seq[1][rl+1:rr]
            braket_include[list_count]=seq[1][rl:rr+1]

            seq[1]=seq[1].replace(seq[1][rl:rr+1],str(list_count))
            list_count+=1
            break
    braket_count-=1
   
# =============================================================================
# Rule 
# =============================================================================

left_step=0
stop=1
time=0
all_path=dict()
m_left=dict()
m_right=dict()
more_nb=0
last_path=dict()
last_nb=0
judge=0
and_one=0

while(stop):
    left_step=0
    right_step=0
    
# =============================================================================
#     Rule 1
# =============================================================================
    
    if '¬' not in seq[0] and '∧' not in seq[0]\
      and '∨' not in seq[0] and '→' not in seq[0]\
        and '↔' not in seq[0]:
            left_step=1
    if '¬' not in seq[1] and '∧' not in seq[1]\
      and '∨' not in seq[1] and '→' not in seq[1]\
        and '↔' not in seq[1] and left_step == 1:
            stop=0
    else:
        left_step=0
    
# =============================================================================
#     Rule P2b 
# =============================================================================
       
    if '¬' in seq[0] and '∧' not in seq[0]\
      and '∨' not in seq[0] and '→' not in seq[0]\
        and '↔' not in seq[0] and left_step==0:
            p_deny=seq[0].index('¬')
            if p_deny == 0 and not seq[1].strip():
                all_path[time] = seq[0] + '⊢' + seq[1] + '  Rule P2b'
                if and_one == 1:
                    all_path[time]=all_path[time][:-10] + ' + ' \
                    + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
                    + all_path[time][-10:]
                    and_one=0          
                seq[1]=seq[1]+seq[0][2]
                seq[0]=seq[0][5:]
                left_step=1
            if p_deny == 0 and seq[1].strip() and left_step == 0:
                all_path[time] = seq[0] + '⊢' + seq[1] + '  Rule P2b'
                if and_one == 1:
                    all_path[time]=all_path[time][:-10] + ' + ' \
                    + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
                    + all_path[time][-10:]
                    and_one=0
                seq[1]=seq[1] + ', ' + seq[0][2]
                seq[0]=seq[0][5:]
                left_step=1
            if p_deny != 0 and not seq[1].strip() and left_step == 0:
                all_path[time] = seq[0] + '⊢' + seq[1] + '  Rule P2b'
                if and_one == 1:
                    all_path[time]=all_path[time][:-10] + ' + ' \
                    + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
                    + all_path[time][-10:]
                    and_one=0
                seq[1]=seq[1]+seq[0][p_deny+2]
                seq[0]=seq[0][:p_deny-2]+seq[0][p_deny+3:]
                left_step=1
            if p_deny != 0 and seq[1].strip() and left_step == 0:
                all_path[time] = seq[0] + '⊢' + seq[1] + '  Rule P2b'
                if and_one == 1:
                    all_path[time]=all_path[time][:-10] + ' + ' \
                    + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
                    + all_path[time][-10:]
                    and_one=0
                seq[1]=seq[1] + ', ' + seq[0][p_deny+2]
                seq[0]=seq[0][:p_deny-2]+seq[0][p_deny+3:]
                left_step=1

# =============================================================================
#     Rule P2a
# =============================================================================
    
    if '¬' in seq[1] and '∧' not in seq[1]\
      and '∨' not in seq[1] and '→' not in seq[1]\
        and '↔' not in seq[1] and left_step==0:
            p_deny_r=seq[1].index('¬')            
            if p_deny_r == 1 and not seq[0].strip() and left_step == 0:                
                all_path[time] = seq[0] + '⊢' + seq[1] + '  Rule P2a'
                if and_one == 1:
                    all_path[time]=all_path[time][:-10] + ' + ' \
                    + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
                    + all_path[time][-10:]
                    and_one=0
                if seq[0]=='':
                    seq[0]=seq[1][3]+' '
                else:
                    seq[0]=seq[1][3]+seq[0]
                seq[1]=seq[1][0]+seq[1][6:]
                left_step=1        
            if p_deny_r == 1 and seq[0].strip() and left_step == 0:
                all_path[time]=seq[0] + '⊢' + seq[1] + '  Rule P2a'
                if and_one == 1:
                    all_path[time]=all_path[time][:-10] + ' + ' \
                    + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
                    + all_path[time][-10:]
                    and_one=0
                seq[0]=seq[0][:-1] + ', ' + seq[1][3] + ' '
                seq[1]=seq[1][0]+seq[1][6:]
                left_step=1               
            if p_deny_r != 1 and not seq[0].strip() and left_step == 0:
                all_path[time] = seq[0] + '⊢' + seq[1] + '  Rule P2a'
                if and_one == 1:
                    all_path[time]=all_path[time][:-10] + ' + ' \
                    + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
                    + all_path[time][-10:]
                    and_one=0
                if seq[0]=='':
                    seq[0]=seq[1][p_deny_r+2]+' '
                else:
                    seq[0]=seq[1][p_deny_r+2]+seq[0]
                seq[1]=seq[1][:p_deny_r-2]+seq[1][p_deny_r+3:]
                left_step=1    
            if p_deny_r != 1 and seq[0].strip() and left_step == 0:
                all_path[time] = seq[0] + '⊢' + seq[1] + '  Rule P2a'
                if and_one == 1:
                    all_path[time]=all_path[time][:-10] + ' + ' \
                    + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
                    + all_path[time][-10:]
                    and_one=0
                seq[0]=seq[0][:-1] + ', ' + seq[1][p_deny_r+2] + ' '
                seq[1]=seq[1][:p_deny_r-2]+seq[1][p_deny_r+3:]
                left_step=1
    
# =============================================================================
#     Rule P3b
# =============================================================================
            
    if '∧' in seq[0] and '∨' not in seq[0] and\
      '→' not in seq[0] and '↔' not in seq[0] and\
        left_step==0:
            p_and_l=seq[0].index('∧')
            all_path[time]=seq[0] + '⊢' + seq[1] + '  Rule P3b'
            if and_one == 1:
                all_path[time]=all_path[time][:-10] + ' + ' \
                + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
                + all_path[time][-10:]
                and_one=0
            seq[0]=seq[0][:p_and_l-1] + ','+ seq[0][p_and_l+1:] 
            left_step=1
            
# =============================================================================
#     Rule P3a
# =============================================================================
    
    if '∧' in seq[1] and '∨' not in seq[1] and\
      '→' not in seq[1] and '↔' not in seq[1] and\
        left_step==0:    
            p_and_r=seq[1].index('∧')
            all_path[time]=seq[0] + '⊢' + seq[1] + '  Rule P3a'
            if and_one == 1:
                all_path[time]=all_path[time][:-10] + ' + ' \
                + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
                + all_path[time][-10:]
                and_one=0
            m_left[more_nb]=seq[0]
            m_right[more_nb]=seq[1][:p_and_r-2]+seq[1][p_and_r+2:]
            seq[1]=seq[1][:p_and_r-1]+seq[1][p_and_r+3:]
            and_one=1
            more_nb+=1
            left_step=1
   
# =============================================================================
#     Rule P4b
# =============================================================================
    
    if '∨' in seq[0] and '→' not in seq[0] and\
      '↔' not in seq[0] and left_step==0:
          p_or_l=seq[0].index('∨')
          all_path[time]=seq[0] + '⊢' + seq[1] + '  Rule P4b'
          if and_one == 1:
              all_path[time]=all_path[time][:-10] + ' + ' \
              + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
              + all_path[time][-10:]
              and_one=0
          m_left[more_nb]=seq[0][:p_or_l-2]+seq[0][p_or_l+2:]
          m_right[more_nb]=seq[1]
          seq[0]=seq[0][:p_or_l-1]+seq[0][p_or_l+3:]
          and_one=1
          more_nb+=1
          left_step=1
        
# =============================================================================
#     Rule P4a
# =============================================================================
    
    if '∨' in seq[1] and '→' not in seq[1] and\
      '↔' not in seq[1] and left_step==0:
          p_or_r=seq[1].index('∨')
          all_path[time]=seq[0] + '⊢' + seq[1] + '  Rule P4a'
          if and_one == 1:
              all_path[time]=all_path[time][:-10] + ' + ' \
              + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
              + all_path[time][-10:]
              and_one=0
          seq[1]=seq[1][:p_or_r-1] + ','+ seq[1][p_or_r+1:] 
          left_step=1
          
# =============================================================================
#     rule P5b
# =============================================================================
    
    if '→' in seq[0] and '↔' not in seq[0] and\
      left_step==0:
          p_imp_l=seq[0].index('→')
          all_path[time]=seq[0] + '⊢' + seq[1] + '  Rule P5b'
          if and_one == 1:
              all_path[time]=all_path[time][:-10] + ' + ' \
              + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
              + all_path[time][-10:]
              and_one=0
          m_left[more_nb]=seq[0][:p_imp_l-2]+seq[0][p_imp_l+5:]
          if not seq[1].strip():
              m_right[more_nb]=seq[1]+seq[0][p_imp_l-2]
          else:
              m_right[more_nb]=seq[1]+', '+seq[0][p_imp_l-2]
          seq[0]=seq[0][:p_imp_l-2]+seq[0][p_imp_l+2:]
          and_one=1
          more_nb+=1
          left_step=1
      
# =============================================================================
#     Rule P5a
# =============================================================================
    
    if '→' in seq[1] and '↔' not in seq[1] and\
      left_step==0:
          p_imp_r=seq[1].index('→')
          if not seq[0].strip() and left_step==0:
              all_path[time]=seq[0] + '⊢' + seq[1] + '  Rule P5a' 
              if and_one == 1:
                  all_path[time]=all_path[time][:-10] + ' + ' \
                  + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
                  + all_path[time][-10:]
                  and_one=0
              if seq[0]=='':
                  seq[0]=seq[1][p_imp_r-2]+' '
              else:
                  seq[0]=seq[1][p_imp_r-2]+seq[0]
                  print(seq[0])
              seq[1]=seq[1][:p_imp_r-2]+seq[1][p_imp_r+2:]    
              left_step=1
          if seq[0].strip() and left_step==0:
              all_path[time]=seq[0] + '⊢' + seq[1] + '  Rule P5a'
              if and_one == 1:
                  all_path[time]=all_path[time][:-10] + ' + ' \
                  + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
                  + all_path[time][-10:]
                  and_one=0
              seq[0]=seq[0][:-1]+', '+seq[1][p_imp_r-2]+' '
              seq[1]=seq[1][:p_imp_r-2]+seq[1][p_imp_r+2:]
              left_step=1
              
# =============================================================================
#     Rule P6b
# =============================================================================
    
    if '↔' in seq[0] and left_step == 0:
        p_iff_l=seq[0].index('↔')
        all_path[time]=seq[0] + '⊢' + seq[1] + '  Rule P6b'
        if and_one == 1:
            all_path[time]=all_path[time][:-10] + ' + ' \
            + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
            + all_path[time][-10:]
            and_one=0
        m_right[more_nb]=seq[1]
        if p_iff_l == 2:
            m_left[more_nb]=seq[0][0]+','+seq[0][p_iff_l+1:]
            if not seq[1].strip():
                
                seq[1]=seq[1]+seq[0][0]+', '+seq[0][p_iff_l+2]
                seq[0]=seq[0][7:]
                if seq[0] == '':
                    seq[0]= ' '

            elif seq[1].strip():
                seq[1]=seq[1]+', '+seq[0][0]+', '+seq[0][p_iff_l+2]
                seq[0]=seq[0][7:]
                if seq[0] == '':
                    seq[0]= ' '
        else:
            m_left[more_nb]=seq[0][:p_iff_l-1]+','+seq[0][p_iff_l+1:]
            if not seq[1].strip():
                seq[1]=seq[1]+seq[0][p_iff_l-2]+', '+seq[0][p_iff_l+2]

                seq[0]=seq[0][:p_iff_l-4]+seq[0][p_iff_l+3:]
            elif seq[1].strip():
                seq[1]=seq[1]+', '+seq[0][p_iff_l-2]+', '+seq[0][p_iff_l+2]
                seq[0]=seq[0][:p_iff_l-4]+seq[0][p_iff_l+3:]
        and_one=1
        more_nb+=1
        left_step=1
        
# =============================================================================
#     Rule P6a
# =============================================================================
    
    if '↔' in seq[1] and left_step == 0:
        p_iff_r=seq[1].index('↔')
        all_path[time]=seq[0] + '⊢' + seq[1] + '  Rule P6a'
        if and_one == 1:
            all_path[time]=all_path[time][:-10] + ' + ' \
            + m_left[more_nb-1] + '⊢' + m_right[more_nb-1]\
            + all_path[time][-10:]
            and_one=0
        m_right[more_nb]=seq[1][:p_iff_r-2]+seq[1][p_iff_r+2:]
        if not seq[0].strip():
            m_left[more_nb]=seq[1][p_iff_r-2]+' '
            seq[0]=seq[1][p_iff_r+2]+ ' '
        elif seq[0].strip():
            m_left[more_nb]=seq[0][:-1]+', '+seq[1][p_iff_r-2]+ ' '
            seq[0]=seq[0][:-1]+ ', '+ seq[1][p_iff_r+2] + ' '
        seq[1]=seq[1][:p_iff_r-1]+seq[1][p_iff_r+3:]
        and_one=1
        more_nb+=1
        left_step=1
                   
# =============================================================================
#     Replace braket
# =============================================================================
          
    if stop == 0:
        for keys,values in list_braket.items():
            reverse_l_nb=len(list_braket)-keys-1
            if str(reverse_l_nb) in seq[0]:
                seq[0]=seq[0].replace(str(reverse_l_nb),list_braket[reverse_l_nb])
                stop=1
                time-=1
                break
    if stop == 0:
        for keys,values in list_braket.items():
            reverse_r_nb=len(list_braket)-keys-1
            if str(reverse_r_nb) in seq[1]:
                seq[1]=seq[1].replace(str(reverse_r_nb),list_braket[reverse_r_nb])
                stop=1
                time-=1
                break
            
# =============================================================================
#     More left or More right
# =============================================================================
    
    if stop == 0:
        if seq[0]=='' or seq[0]==' ' or seq[1]=='' or seq[1]==' ':
            print(False)
            judge=1
            break
        all_path[time]=seq[0] + '⊢' + seq[1] + '  Rule 1'
        last_nb+=1
        if len(m_left)!=0:
            for key, value in m_left.items():
                seq[0]=value
                m_left.pop(key)
                break
            for keys, values in m_right.items():
                seq[1]=values
                m_right.pop(keys)
                break
            stop=1
    time+=1

# =============================================================================
# Print all_path
# =============================================================================

if judge==0:
    k=len(list_braket)
    print(True)
    while k:
        for keys,values in braket_include.items():
            for key,value in all_path.items():
                if str(keys) in all_path[key][:-5]:                    
                    all_path[key]=all_path[key][:-5].replace(str(keys),braket_include[keys]) + all_path[key][-5:]
        k-=1
    for i in range(len(all_path)):
        print(str(i+1)+'    '+all_path[len(all_path)-1-i])
    print('QED.')

