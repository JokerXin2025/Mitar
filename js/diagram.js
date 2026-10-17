document.addEventListener("DOMContentLoaded",function(){
    document.querySelectorAll('.diagram-figure .diagram-zoom').forEach(updateZoom);
});
function updateZoom(input){
    var p = parseInt(input.value), s = p/100;
    var fig = input.closest('.diagram-figure');
    fig.querySelector('.diagram-zoom-stage svg').style.transform = 'scale(' + s + ')';
    fig.querySelector('.diagram-zoom-value').textContent = p + '%';
}
