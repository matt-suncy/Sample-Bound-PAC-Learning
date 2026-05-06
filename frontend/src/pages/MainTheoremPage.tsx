import { useState } from 'react'
import Navigation from '../components/Navigation'
import DependencyGraph from '../components/DependencyGraph'
import CodePopup from '../components/CodePopup'
import type { TheoremNodeData } from '../data/graphData'

export default function MainTheoremPage() {
  const [codeNode, setCodeNode] = useState<TheoremNodeData | null>(null)

  return (
    <div className="flex flex-col min-h-screen" style={{ background: '#FAFAFA' }}>
      <Navigation />

      {/* Page title */}
      <div
        className="text-center"
        style={{ paddingTop: '5rem', paddingBottom: '2rem', flexShrink: 0 }}
      >
        <h1
          className="font-inter font-bold text-[#111111]"
          style={{ fontSize: '3rem', lineHeight: 1.1, margin: 0 }}
        >
          Main Theorem
        </h1>
        <p
          className="font-inter text-[#888888] mt-3"
          style={{ fontSize: '0.875rem' }}
        >
          Click a node to view its Lean code. Hover to see its natural language statement.
        </p>
      </div>

      {/* Graph — ReactFlow requires explicit pixel height on its parent */}
      <div style={{ width: '100%', height: 'calc(100vh - 180px)' }}>
        <DependencyGraph onNodeClick={setCodeNode} />
      </div>

      {codeNode && (
        <CodePopup node={codeNode} onClose={() => setCodeNode(null)} />
      )}
    </div>
  )
}
