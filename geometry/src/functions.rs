/// Return the distance between `point` and the straight line ax + by + c = 0 exlained by `coef`.
pub fn distance_point_to_straight_line(point: (f64, f64), coef: (f64, f64, f64)) -> f64 {
    let (x, y) = point;
    let (a, b, c) = coef;
    (a * x + b * y + c).abs() / a.hypot(b)
}

/// Return the distance between `point` and the segment line started from `start` and terminated at `end`.
pub fn distance_point_to_segment_line(point: (f64, f64), start: (f64, f64), end: (f64, f64)) -> f64 {
    let (x0, y0) = point;
    let (x1, y1) = start;
    let (x2, y2) = end;
    let a = x2 - x1;
    let b = y2 - y1;
    let a2 = a * a;
    let b2 = b * b;
    let r2 = a2 + b2;
    let tt = -(a * (x1 - x0) + b * (y1 - y0));
    if tt < 0.0 {
        (x1 - x0) * (x1 - x0) + (y1 - y0) * (y1 - y0)
    } else if tt > r2 {
        (x2 - x0) * (x2 - x0) + (y2 - y0) * (y2 - y0)
    } else {
        let f1 = a * (y1 - y0) - b * (x1 - x0);
        (f1 * f1) / r2
    }
}

/// Convert the pair of `start` and `end` to the coefficients for straight line ax + by + c = 0.<br/>
/// Return (a, b, c)
pub fn points_to_line_coef(start: (f64, f64), end: (f64, f64)) -> Option<(f64, f64, f64)> {
    let (x, y) = start;
    let (tx, ty) = end;

    if (x - tx).abs() < 1e-8 {
        return None;
    }

    let a = (ty - y) / (tx - x);
    let b = 1.0;
    let c = y - a * x;
    Some((a, b, c))
}
