import { BrowserRouter, Routes, Route, Navigate } from 'react-router-dom'
import Home from './pages/Home'
import MainTheoremPage from './pages/MainTheoremPage'
import AboutPage from './pages/AboutPage'
import MethodsPage from './pages/MethodsPage'

export default function App() {
  return (
    <BrowserRouter>
      <Routes>
        <Route path="/" element={<Home />} />
        <Route path="/main-theorem" element={<MainTheoremPage />} />
        <Route path="/about" element={<AboutPage />} />
        <Route path="/methods" element={<MethodsPage />} />
        <Route path="*" element={<Navigate to="/" replace />} />
      </Routes>
    </BrowserRouter>
  )
}
