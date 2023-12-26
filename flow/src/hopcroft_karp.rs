use std::collections::VecDeque;

// reference: https://ngtkana.hatenablog.com/entry/2023/01/21/104159
/// Return the edge set that constitutes the maximal matching of the bipartite graph formed by `edges`.  <br/>
/// `edges` takes (left-group, right-group), where both left and right are 0-based indices.
#[doc(alias = "maximum_matching_of_bipartite_graph")]
pub fn hopcroft_karp(edges: &[(usize, usize)]) -> Vec<(usize, usize)> {
    if edges.is_empty() {
        return vec![];
    }

    let left = edges.iter().map(|&(i, _)| i).max().unwrap() + 1;
    let right = edges.iter().map(|&(_, j)| j).max().unwrap() + 1;
    let mut g = vec![vec![]; left];
    let mut h = vec![usize::MAX; right];
    edges.iter().for_each(|&(i, j)| g[i].push(j));

    while {
        let mut dist = vec![0usize; left];
        h.iter()
            .filter(|&&h| h < usize::MAX)
            .for_each(|&i| dist[i] = usize::MAX);
        let mut queue = (0..left).filter(|&i| dist[i] == 0).collect::<VecDeque<_>>();
        while let Some(i) = queue.pop_front() {
            for i1 in g[i]
                .iter()
                .filter_map(|&j| (h[j] < usize::MAX).then_some(h[j]))
            {
                if dist[i1] == usize::MAX {
                    dist[i1] = dist[i] + 1;
                    queue.push_back(i1);
                }
            }
        }
        (0..left)
            .map(|i| dist[i] == 0 && path(&g, &mut h, &mut dist, i))
            .fold(false, std::ops::BitOr::bitor)
    } {}
    h.iter()
        .enumerate()
        .filter_map(|(j, &i)| (i < usize::MAX).then_some((i, j)))
        .collect::<Vec<_>>()
}

fn path(g: &[Vec<usize>], h: &mut [usize], dist: &mut [usize], i: usize) -> bool {
    let d = std::mem::replace(&mut dist[i], !0);
    g[i].iter()
        .copied()
        .find(|&j| h[j] == usize::MAX || (d + 1 == dist[h[j]] && path(g, h, dist, h[j])))
        .into_iter()
        .inspect(|&j| h[j] = i)
        .next()
        .is_some()
}
