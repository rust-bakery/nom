//#![feature(trace_macros)]
#![feature(test)]
extern crate test;

#[macro_use]
extern crate nom;

use test::Bencher;


named!(test_take_until_and_consume, take_until_and_consume!("fermentum."));

#[bench]
fn take_until_and_consume_bench(b: &mut Bencher) {
  let data = &b"Lorem ipsum dolor sit amet, consectetur adipiscing elit. Vestibulum id tortor sed
    quam tristique congue vel eu nisi. Ut nec lacus diam. Praesent pellentesque turpis tortor,
    eget finibus massa tincidunt et. Morbi et iaculis est. Fusce nunc augue, dapibus id fringilla
    nec, posuere sed leo. Sed non aliquam sapien, vel dictum felis. Aliquam elementum velit
    ac turpis vestibulum mattis. Cras auctor at leo sit amet vulputate. In nec fermentum
    nulla. Integer egestas lacinia porttitor. Fusce sodales mi quis urna eleifend, vitae
    lacinia magna consequat. Fusce ex felis, ultricies non condimentum eget, condimentum nec
    arcu. Duis non tempor lacus. Ut consequat, dui in consequat placerat, purus orci interdum
    quam, eu finibus tortor velit quis augue. Pellentesque nec mollis tortor. Pellentesque
    cursus faucibus sapien quis blandit.

    Ut nisi ex, scelerisque sed mollis sit amet, hendrerit sit amet mauris. Interdum et malesuada
    fames ac ante ipsum primis in faucibus. Cras eu nisi eu sem commodo placerat. Lorem ipsum dolor
    sit amet, consectetur adipiscing elit. Duis faucibus nisi id fringilla elementum. Nullam
    suscipit ipsum ut tortor dictum, quis auctor dolor consectetur. Vivamus posuere laoreet sem in
    semper. Nullam quis orci non felis dapibus tempus sit amet ut lorem.

    Nam tincidunt erat a vulputate cursus. Donec in ligula pharetra ipsum fringilla maximus. Nulla
    sollicitudin, nibh at tempor bibendum, mi arcu pulvinar augue, id vulputate turpis mi eget
    justo. Sed maximus sed massa vitae blandit. Integer nec diam ex. Aliquam accumsan massa ut ex
    volutpat lobortis. Aliquam erat volutpat. Curabitur in lorem nisi. Nam non eros sollicitudin,
    luctus ante et, hendrerit lectus. Nam pellentesque sapien est, quis lacinia massa auctor vel.
    Donec ac vehicula magna. Pellentesque habitant morbi tristique senectus et netus et malesuada
    fames ac turpis egestas. In hac habitasse platea dictumst. Curabitur et sem vitae ipsum
    vestibulum ullamcorper nec et diam. Fusce sagittis nisi et dolor semper mollis.

    Sed aliquet consequat sagittis. Ut quis velit dictum, iaculis diam vel, lobortis quam. Maecenas
    quis blandit sem. Fusce a volutpat nunc. Aliquam nec purus in libero commodo pharetra commodo
    in massa. Donec non dictum elit, non mollis enim. In consectetur ligula ac justo tincidunt,
    quis varius felis auctor. Nunc sit amet eleifend ante, at vulputate justo. In convallis diam
    quis magna laoreet bibendum. Pellentesque varius faucibus pretium. Phasellus nec est eleifend,
    malesuada lacus ornare, suscipit justo. Integer eu massa ut sapien congue ullamcorper eget non
    neque. Mauris vitae libero velit. Class aptent taciti sociosqu ad litora torquent per conubia
    nostra, per inceptos himenaeos. Nunc ac tortor feugiat, volutpat dolor vitae, viverra quam.
    Suspendisse dictum auctor purus nec molestie.

    Fusce egestas, est a efficitur facilisis, neque diam tincidunt dui, nec pellentesque risus
    augue eget mauris. Cras iaculis tincidunt semper. Vestibulum venenatis id ligula a cursus.
    Pellentesque pharetra, magna et porttitor consectetur, ligula lectus sodales tellus, ac
    convallis dui justo et lorem. Nulla rhoncus porta facilisis. In quis risus rutrum nunc
    fermentum lacinia. Sed ac quam mauris. Morbi sodales dui ac ullamcorper porttitor. Donec id
    lacus neque. Phasellus porta quam a ante fringilla fermentum. ";

  b.iter(||{
    test_take_until_and_consume(&data[..])
  });
}

