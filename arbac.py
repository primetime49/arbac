import copy
import time
import multiprocessing

# To parse input formatted in <xx,xx,...>
def read_bracket(br):
    res = br[1:-1].split(',')
    return res

# To parse requests formatted in pos&pos&...&-neg
def read_reqs(reqs):
    if reqs == 'TRUE':
        return ([],[])
    else:
        pos = []
        neg = []
        reqs = reqs.split('&')
        for r in reqs:
            if r[0] == '-':
                neg.append(r[1:])
            else:
                pos.append(r)
        return(pos,neg)

# To check if big array contains ALL elements in small array
def contains(big,small):
    for s in small:
        if s not in big:
            return False
    return True

# To check if big array doesn't contain ANY elements in small array
def not_contains(big,small):
    for s in small:
        if s in big:
            return False
    return True

# Search for every CA rule that can assign this target role
def find_assigned(target):
    res = []
    for c in ca:
        if target in ca[c]:
            res.append((c,ca[c][target]))
    return res

inp = input('policy number? ')
file1 = open('policy'+str(inp)+'.arbac', 'r')
lines = file1.readlines()

roles = lines[0].split(' ')[1:-1]
users = lines[2].split(' ')[1:-1]
ua = lines[4].split(' ')[1:-1]
cr = lines[6].split(' ')[1:-1]
ca = lines[8].split(' ')[1:-1]
goal = lines[10].split(' ')[1:-1][0]

# Generate user_role dictionary {'user1': ['role1', 'role2',...], ...}
user_role = dict()
for u in users:
    user_role[u] = []

for n in ua:
    name,role = read_bracket(n)
    user_role[name].append(role)

# transform CA to a dictionary in format:
# {
#   'ra1':
#     'rt1':
#       ([pos1, pos2,...], [neg1, neg2,...])
#     'rt2:
#     ...
#   'ra2':
#   ...
# }
tmp = dict()
for n in ca:
    src,reqs,dst = read_bracket(n)
    if src in tmp:
        tmp[src][dst] = read_reqs(reqs)
    else:
        tmp[src] = dict()
        tmp[src][dst] = read_reqs(reqs)
ca = tmp

# transform CR to a dictionary in format:
# {'ra1': ['rt1','rt2',...], ...}
tmp = dict()
for n in cr:
    src,dst = read_bracket(n)
    if src in tmp:
        tmp[src].append(dst)
    else:
        tmp[src] = []
        tmp[src].append(dst)
cr = tmp

# forward slicing
s = dict()
for u in user_role:
    for a in user_role[u]:
        s[a] = ''
changed = True
while changed:
    changed = False
    for src in ca:
        for dst in ca[src]:
            if contains(s,ca[src][dst][0]+[src]):
                if dst not in s:
                    s[dst] = ''
                    changed = True

# generate the R/S*                
rs = []
for r in roles:
    if r not in s:
        rs.append(r)

# backward slicing
s = dict()
s['target'] = ''

changed = True
while changed:
    changed = False
    add = []
    for si in s:
        for f in find_assigned(si):
            add += [f[0]] + f[1][0] + f[1][1]
    for a in add:
        if a not in s:
            s[a] = ''
            changed = True

# generate the R/S*
for r in roles:
    if r not in s:
        rs.append(r)    

# simplification algorithms on the fixpoint S* after backward slicing
# delete CA that assign a role in R/S*
rem = []
remm = []

for src in ca:
    for dst in ca[src]:
        if dst in rs:
            rem.append((src,dst))

for r in rem:
    del(ca[r[0]][r[1]])

for src in ca:
    if len(ca[src]) == 0:
        remm.append(src)
        
for r in remm:
    del(ca[r])

# delete CR that revoke a role in R/S*
rem = []
remm = []

for src in cr:
    for dst in cr[src]:
        if dst in rs:
            rem.append((src,dst))

for r in rem:
    cr[r[0]].remove(r[1])

for src in cr:
    if len(cr[src]) == 0:
        remm.append(src)
        
for r in remm:
    del(cr[r])
    
for r in rs:
    roles.remove(r)
    
# delete roles in R/S*
rem = []
remm = []
for u in user_role:
    for r in user_role[u]:
        if r in rs:
            rem.append((u,r))
for r in rem:
    user_role[r[0]].remove(r[1])

for u in user_role:
    if len(user_role[u]) == 0:
        remm.append(u)
        
for r in remm:
    del(user_role[r])
    
print('Processing...')
def analyzer(ur,ctr,use_cr=True):
    # for all user
    for user in ur:
        if (ctr == 0):
            print(user)
        # for all of their assigned roles
        for i in range(len(ur[user])):
            # we try to see if that role can assign other roles, a.k.a it is an administrative role
            ra = ur[user][i]
            # we're checking it to every other users
            for u in ur:
                if ra in ca:
                    for rt in ca[ra]:
                        # if it is an administrative role, see if the target user can be assigned the target role
                        if contains(ur[u],ca[ra][rt][0]) and not_contains(ur[u],ca[ra][rt][1]):
                            if rt not in ur[u]:
                                if rt == goal:
                                    return True
                                # assign the rule, and recursively call the function again
                                old = copy.deepcopy(ur)
                                ur[u].append(rt)
                                if analyzer(ur,1,use_cr) == True:
                                    return True
                                ur = old
                # this one is to see if that role can revoke other roles
                if ra in cr and use_cr:
                    for rt in cr[ra]:
                        # if it can, and the target user has that role, we revoke them and call recursive again
                        if rt in ur[u]:
                            old = copy.deepcopy(ur)
                            ur[u].remove(rt)
                            if analyzer(ur,1,use_cr) == True:
                                return True
                            ur = old
                            
use_cr = input('Do you want to use Can-Revoke rules? [y/n] ')
def main(use_cr):        
    start = time.time()
    if use_cr == 'y':
        use_cr = True
    else:
        use_cr = False
    try:
        if analyzer(copy.deepcopy(user_role),0,use_cr) == True:
            print('Got result!')
            print('1')
        else:
            print('Got result!')
            print('0')
    except RecursionError:
        print('We got a cycle!')
        print('Exiting the code...')
    print("Time elapsed: {} seconds".format(round(time.time() - start,4)))

# ref: https://stackoverflow.com/questions/14920384/stop-code-after-time-period
# to stop program if running more than 10 seconds, adjustable here.
p = multiprocessing.Process(target=main, name="Main", args=(use_cr,))
p.start()

# Wait a maximum of 10 seconds for foo
# Usage: join([timeout in seconds])
p.join(10)

# If thread is active
if p.is_alive():
    print("Killed after 10s")

    # Terminate foo
    p.terminate()
    p.join()