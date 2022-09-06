fn dfs(now: usize, g: i32, stack: &mut Vec<usize>, group: &mut Vec<i32>, t: &Vec<Vec<usize>>) {
    group[now] = g;
    for to in &t[now] {
        if group[*to] < 0 {
            dfs(*to, g, stack, group, t);
        }
    }
    stack.push(now);
}

fn dfs2(now: usize, g: i32, group: &Vec<i32>, s: &mut Vec<i32>, r: &Vec<Vec<usize>>) {
    s[now] = g;
    for to in &r[now] {
        if group[now] == group[*to] && s[*to] < 0 {
            dfs2(*to, g, group, s, r);
        }
    }
}

#[allow(dead_code)]
// Return the array of each vertex with ID for each strongly connected component
pub fn scc(n: usize, edges: &Vec<(usize, usize)>) -> Vec<i32> {
    let mut t = vec![vec![]; n];
    let mut rt = vec![vec![]; n];
    for (a, b) in edges {
        t[*a].push(*b);
        rt[*b].push(*a);
    }
    let mut group = vec![-1; n];
    let mut v = vec![];
    let mut g = 0;
    for i in 0..n {
        if group[i] < 0 {
            let mut stack = vec![];
            dfs(i, g, &mut stack, &mut group, &t);
            g += 1;
            v.push(stack);
        }
    }
    let mut g = 0;
    let mut res = vec![-1; n];
    for w in v.iter_mut() {
        while let Some(now) = w.pop() {
            if res[now] < 0 {
                dfs2(now, g, &group, &mut res, &rt);
                g += 1;
            }
        }
    }
    res
}

#[cfg(test)]
mod tests {
    use super::{
        scc
    };

    #[test]
    fn scc_test() {
        let edges = 
            vec![
                (0, 1),
                (1, 2),
                (2, 3), (2, 5),
                (3, 0),
                (4, 0),
                (5, 8),
                (6, 4), (6, 7),
                (7, 4),
                (8, 3)
            ];
        
        let groups = scc(9, &edges);

        assert_eq!(groups[0], groups[1]);
        assert_eq!(groups[0], groups[2]);
        assert_eq!(groups[0], groups[3]);
        assert_eq!(groups[0], groups[5]);
        assert_eq!(groups[0], groups[8]);
        assert_ne!(groups[0], groups[4]);
        assert_ne!(groups[4], groups[6]);
        assert_ne!(groups[4], groups[7]);
        assert_ne!(groups[6], groups[7]);
    }
}