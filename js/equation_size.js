function autoScaleMath() {
    // 获取所有的公式容器
    const mathContainers = document.querySelectorAll('.step-lhs, .step-rhs');
    mathContainers.forEach(container => {
        // 恢复初始状态以便测量真实宽度
        container.style.transform = 'scale(1)';
        // offsetWidth 是容器给定的宽度，scrollWidth 是公式实际需要的宽度
        const availableWidth = container.offsetWidth;
        const actualWidth = container.scrollWidth;
        if (actualWidth > availableWidth && availableWidth > 0) {
            container.style.transform = `scale(${availableWidth / actualWidth})`;
        }
    });
}
// 1. 页面加载时执行一次
window.addEventListener('load', autoScaleMath);
// 2. 监听窗口大小改变，实时缩放
window.addEventListener('resize', autoScaleMath);

document.addEventListener("DOMContentLoaded", function() {
    renderMathInElement(document.body, {
        delimiters: [
            {left: "$$", right: "$$", display: true},
            {left: "$", right: "$", display: false}
        ]
    });
    autoScaleMath();
});